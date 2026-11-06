import contextlib
import io
import subprocess
import sys
import tempfile
import unittest
import zipfile
from pathlib import Path
from unittest.mock import patch

import file_bmo_bug as filer


class FilerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.finding = self.root / "high" / "ANT-2026-TEST"
        self.finding.mkdir(parents=True)
        (self.finding / "REPORT.md").write_text(
            "ANT-2026-TEST [high]\nExample finding\n\n"
            "## Reproducing\nRun `/tmp/repro` in `/src`.\n\n"
            "## Suggested fix\nPrivate patch details.\n"
        )
        (self.finding / "repro").write_text("# /tmp/repro.d/example\n")

    def unzip(self, data):
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            return {name: archive.read(name) for name in archive.namelist()}

    def test_report_and_finding(self):
        report = (self.finding / "REPORT.md").read_text()
        self.assertEqual(filer.find_finding(self.root, "test"), self.finding)
        self.assertEqual(filer.parse_report(report), ("ANT-2026-TEST", "Example finding"))
        description = filer.build_description(report)
        self.assertIn("Run `repro.py` in the pdf.js checkout.", description)
        self.assertNotIn("Suggested fix", description)

    def test_reproducer_archive(self):
        reprod = self.finding / "repro.d"
        (reprod / "nested").mkdir(parents=True)
        (reprod / "__pycache__").mkdir()
        (reprod / "__pycache__" / "ignored.pyc").write_bytes(b"ignored")
        (reprod / "nested" / "helper.py").write_bytes(b"path = '/tmp/repro.d/data'")
        (reprod / "input.pdf").write_bytes(b"%PDF-/tmp/repro.d")
        attachments = filer.collect_attachments(self.finding, "TEST", [])
        self.assertEqual(len(attachments), 1)
        self.assertEqual(self.unzip(attachments[0]["data"]), {
            "repro.py": b"# ./example\n",
            "nested/helper.py": b"path = './data'",
            "input.pdf": b"%PDF-/tmp/repro.d",
        })

    def test_pdf_attachment_threshold(self):
        for count in (0, filer.MAX_SEPARATE_PDFS, filer.MAX_SEPARATE_PDFS + 1):
            with self.subTest(count=count):
                pdfs = [(f"{i}.pdf", b"%PDF-test") for i in range(count)]
                attachments = filer.collect_attachments(self.finding, "TEST", pdfs)
                if count > filer.MAX_SEPARATE_PDFS:
                    self.assertEqual(len(attachments), 2)
                    self.assertEqual(self.unzip(attachments[0]["data"]), dict(pdfs))
                else:
                    self.assertEqual(len(attachments), count + 1)
                    self.assertEqual([a["data"] for a in attachments[:-1]],
                                     [data for _, data in pdfs])

    def test_attachment_limits(self):
        with patch.object(filer, "MAX_ATTACHMENT_SIZE", 200):
            attachment = filer.make_attachment("large.pdf", "x" * 251, b"x" * 1000)
            self.assertEqual(attachment["file_name"], "large.pdf.zip")
            self.assertEqual(attachment["content_type"], "application/zip")
            self.assertEqual(attachment["summary"], "x" * 249 + "…")
            self.assertEqual(self.unzip(attachment["data"]), {"large.pdf": b"x" * 1000})
            with contextlib.redirect_stderr(io.StringIO()) as warnings:
                self.assertIsNone(filer.make_attachment("large.zip", "archive", b"x" * 201))
            self.assertIn("is not attached", warnings.getvalue())

    def test_generation_deduplicates_and_preserves_labels(self):
        reprod = self.finding / "repro.d"
        reprod.mkdir()
        (reprod / "input.pdf").write_bytes(b"%PDF-original")
        (reprod / "helper.py").write_text(
            "from pathlib import Path\nPath('helper.pdf').write_bytes(b'%PDF-helper')\n"
        )
        (self.finding / "repro").write_text("""
import subprocess
from pathlib import Path
first_pdf = b'%PDF-first'
second_pdf = b'%PDF-second'
for directory, data in [('a', first_pdf), ('b', second_pdf)]:
    Path(directory).mkdir()
    Path(directory, 'test.pdf').write_bytes(data)
Path('raw').write_bytes(b'%PDF-raw')
Path('empty.pdf').write_bytes(b'')
Path('notes.txt').write_text('not a PDF')
existing = Path('/tmp/repro.d/input.pdf').read_bytes()
Path('copy.pdf').write_bytes(existing)
subprocess.run(['node', 'blocked.js'])
Path('after.pdf').write_bytes(b'%PDF-after')
subprocess.run(['python3', '/tmp/repro.d/helper.py'], check=True)
memory_pdf = b'%PDF-memory'
""")
        pdfs = filer.generate_pdfs(self.finding, self.root / "run", 10, False)
        self.assertEqual(dict(pdfs), {
            "first.pdf": b"%PDF-first", "second.pdf": b"%PDF-second",
            "raw.pdf": b"%PDF-raw", "after.pdf": b"%PDF-after",
            "helper.pdf": b"%PDF-helper", "memory.pdf": b"%PDF-memory",
        })
        self.assertEqual(len(pdfs), 6)

    def test_generation_timeout_keeps_written_pdfs(self):
        (self.finding / "repro").write_text(
            "from pathlib import Path\n"
            "Path('ready.pdf').write_bytes(b'%PDF-ready')\n"
            "sum(iter(int, 1))\n"
        )
        with contextlib.redirect_stderr(io.StringIO()) as output:
            pdfs = filer.generate_pdfs(self.finding, self.root / "run", 1, True)
        self.assertEqual(pdfs, [("ready.pdf", b"%PDF-ready")])
        self.assertIn("stopped after 1 s", output.getvalue())

    def test_dry_run(self):
        result = subprocess.run(
            [sys.executable, filer.__file__, "--root", str(self.root), "--id", "TEST",
             "--no-pdf", "--dry-run", "--security"],
            capture_output=True, text=True, check=True,
        )
        output = next(line.removeprefix("Description and attachments written to ")
                      for line in result.stdout.splitlines()
                      if line.startswith("Description and attachments written to "))
        self.addCleanup(filer.shutil.rmtree, Path(output).parent)
        self.assertIn("Security: yes", result.stdout)
        self.assertTrue((Path(output) / "ANT-2026-TEST-reproducer.zip").is_file())
        self.assertIn("repro.py", (Path(output) / "description.md").read_text())


if __name__ == "__main__":
    unittest.main()
