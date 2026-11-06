#!/usr/bin/env python3
"""File an OSS-scanner finding as a bug in Firefox :: PDF Viewer on Bugzilla."""

import argparse
import ast
import base64
import builtins
import hashlib
import io
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from collections import Counter
from pathlib import Path

DEFAULT_BUGZILLA_URL = "https://bugzilla.mozilla.org"
DEFAULT_TOKEN_FILE = "~/.bz"
PRODUCT = "Firefox"
COMPONENT = "PDF Viewer"
FALLBACK_SECURITY_GROUP = "firefox-core-security"
SECURITY_META_BUG = 2085716
SECURITY_FOLDERS = {"critical", "high", "medium", "low"}
MAX_ATTACHMENT_SIZE = 10 * 1024 * 1024
MAX_COMMENT_LENGTH = 65535
MAX_SEPARATE_PDFS = 6
GENERATION_TIMEOUT = 180

TEXT_SUFFIXES = {
    ".py", ".mjs", ".js", ".cjs", ".html", ".htm", ".xml", ".xdp", ".txt",
    ".md", ".json", ".css", ".svg", ".patch", ".diff", ".sh", ".ps", ".ftl",
}
INFRA_SCRIPT_RE = re.compile(
    r"^(serve|start_|firefox_with|launch_|headless_|chrome_|open_|visit_)"
    r"|_(site|server)\.py$|server"
)

# Rewrites of the "Reproducing" section: the reports describe a docker image
# with the checkout in /src and the companion files in /tmp/repro.d.
REPRODUCING_REWRITES = [
    (r"\s*\(`cp -r repro\.d /tmp/repro\.d[^)]*\)", ""),
    (r"`cp -r repro\.d /tmp/repro\.d[^`]*`", "`python3 repro.py`"),
    (
        r"cp -r repro\.d /tmp/repro\.d && cp repro /tmp/repro && cd /src && /tmp/repro",
        "python3 repro.py",
    ),
    (
        r"\b([Ff])iles in `(?:/tmp/)?repro\.d/?`",
        r"\1iles in the attached reproducer archive",
    ),
    (
        r"\b(?:in|from|under|at) `(?:/tmp/)?repro\.d/?`",
        "in the attached reproducer archive",
    ),
    (r"`(?:/tmp/)?repro\.d/?`", "the attached reproducer archive"),
    (r"(?:/tmp/)?repro\.d/", ""),
    (r"`(?:/tmp/)?repro`", "`repro.py`"),
    (r"\bas built in the image\b", "as built from the checkout"),
    (
        r",?\s*\b(?:that|which) (?:is|was) (?:already )?"
        r"(?:built |installed |prebuilt )?in the image\b",
        "",
    ),
    (r",?\s*\b(?:that ships|as it is) in the image\b", ""),
    (r"\s*\b(?:already )?(?:built |installed |prebuilt )?in the image\b", ""),
    (r"\bnothing but the image\b", "nothing but a built pdf.js checkout"),
    (r"\b(Firefox Nightly) of the image\b", r"\1"),
    (r"\(the image's was built", "(the prebuilt one was built"),
    (
        r"\bthe image's\s+(?=`build|`/src|`TESTING|prebuilt |Firefox|headless|"
        r"existing|built |Node\.js|own )",
        "the ",
    ),
    (r"\bcd /src && ", ""),
    (r"\bcwd=/src\b", "cwd set to the pdf.js checkout"),
    (r"`/src`", "the pdf.js checkout"),
    (r"`/src/", "`"),
    (r"(?<![\w./])/src/", ""),
    (r"`/tmp/([^`/\s]+)`", r"`\1`"),
]


SKIPPED_DIRS = {"repro.d", "patches", "node_modules", "__pycache__"}


def find_finding(root, ident):
    ident = ident.strip().upper()
    root = root.expanduser().resolve()
    if not root.is_dir():
        sys.exit(f"{root} is not a directory")

    def is_finding(path):
        name = path.name.upper()
        return (name == ident or name.endswith("-" + ident)) and \
            (path / "REPORT.md").is_file()

    if is_finding(root):
        return root
    matches = []
    for dirpath, dirnames, _ in os.walk(root):
        dirnames[:] = sorted(
            d for d in dirnames if not d.startswith(".") and d not in SKIPPED_DIRS
        )
        for name in list(dirnames):
            path = Path(dirpath, name)
            if is_finding(path):
                matches.append(path)
                dirnames.remove(name)
    if not matches:
        sys.exit(f"No finding {ident!r} under {root}")
    if len(matches) > 1:
        sys.exit(f"{ident!r} is ambiguous: " + ", ".join(str(m) for m in matches))
    return matches[0]


def parse_report(text):
    m = re.search(r"^(ANT-\d{4}-[A-Z0-9]+)[ \t]+\[[^\n]*\n([^\n]+)$", text, re.M)
    if not m:
        sys.exit("Unable to find the id and title in the report header")
    return m[1], m[2].strip()


def split_sections(text):
    parts = re.split(r"(?m)^(?=## )", text)
    return [(p.split("\n", 1)[0][3:].strip() if p.startswith("## ") else None, p)
            for p in parts]


PATCH_SENTENCE_RE = re.compile(
    r"^(?:With(?:out)? (?:(?:the|either|both) )?(?:attached )?patch(?:es)?\b"
    r"|(?:The|This) attached (?:\w+ )?patch\b|Attached patch\b"
    r"|The patch attached here\b|Two candidate patches\b"
    r"|(?:A|An|On a|In a|Against a)\b[^,]{0,100}\bwith the attached patch\b"
    r"|(?:A|An|The)\b.*\b(?:patch|fix)(?:es)?\b.*\b(?:is|are) (?:also )?attached\b)",
    re.I,
)
NON_PROSE_RE = re.compile(r"(?m)^(?:\s*(?:[*+|>-]|\d+\.)\s|    |#)")


def drop_patch_sentences(text):
    out = []
    in_code = False
    drop_list = False
    for part in re.split(r"(\n[ \t]*\n)", text):
        if not part.strip():
            out.append(part)
            continue
        fences = part.count("```")
        skip = in_code or fences or NON_PROSE_RE.search(part)
        if fences % 2:
            in_code = not in_code
        if drop_list and re.match(r"\s*(?:[*+-]|\d+\.)\s", part):
            drop_list = False
            continue
        drop_list = False
        if skip:
            out.append(part)
            continue
        sentences = re.split(r"(?<=[.!?:])\s+(?=[A-Z`(])", part.strip())
        kept = [x for x in sentences
                if not PATCH_SENTENCE_RE.search(" ".join(x.split()))]
        if len(kept) == len(sentences):
            out.append(part)
            continue
        drop_list = sentences[-1] not in kept and sentences[-1].endswith(":")
        out.append(" ".join(" ".join(x.split()) for x in kept))
    return re.sub(r"\n{3,}", "\n\n", "".join(out))


def adapt_reproducing(section):
    for pattern, replacement in REPRODUCING_REWRITES:
        section = re.sub(pattern, replacement, section)
    return section


def build_description(text):
    out = []
    for title, section in split_sections(text):
        if title in ("Running the reproducer", "Suggested fix"):
            continue
        if title == "Reproducing":
            section = adapt_reproducing(section)
        out.append(section)
    return drop_patch_sentences("".join(out)).rstrip() + "\n"


def adapt_attached_file(data):
    return data.replace(b"/tmp/repro.d", b".")


def content_type_for(name):
    suffix = Path(name).suffix.lower()
    if suffix == ".pdf":
        return "application/pdf"
    if suffix == ".zip":
        return "application/zip"
    if suffix in TEXT_SUFFIXES or suffix == "":
        return "text/plain"
    return "application/octet-stream"


def read_pdf(path):
    """Read a PDF once, checking only the header for files without a PDF suffix."""
    with path.open("rb") as f:
        header = f.read(1024)
        if path.suffix.lower() == ".pdf" or b"%PDF-" in header:
            return header + f.read()
    return None


# --- PDF generation ---------------------------------------------------------
#
# The reproducer is run in a child process with every external program (node,
# Firefox, gulp, servers, ...) blocked; only the Python generators shipped with
# it (and openssl) are allowed to run. Every statement is made non-fatal, so the
# script goes on writing its PDFs when a blocked call fails.


class _Blocked(Exception):
    pass


class _LoopGuard(Exception):
    pass


ALLOWED_PROGRAMS = {"openssl"}


class _Resilient(ast.NodeTransformer):
    def __init__(self, sandbox, wrap=True):
        self.reprod = str(sandbox / "repro.d")
        self.repro = str(sandbox / "repro")
        self.tmp = str(sandbox / "tmp")
        self.wrap = wrap

    def visit_Constant(self, node):
        value = node.value
        if isinstance(value, str):
            if value.startswith("/tmp/repro.d"):
                value = self.reprod + value[len("/tmp/repro.d"):]
            elif value == "/tmp/repro":
                value = self.repro
            elif value == "/tmp" or value.startswith("/tmp/"):
                value = self.tmp + value[len("/tmp"):]
            node.value = value
        return node

    @staticmethod
    def _assigned_names(stmt):
        if isinstance(stmt, ast.Assign):
            targets = stmt.targets
        elif isinstance(stmt, ast.AnnAssign):
            targets = [stmt.target]
        else:
            return []
        names = []
        for target in targets:
            nodes = target.elts if isinstance(target, (ast.Tuple, ast.List)) else [target]
            names += [n.id for n in nodes if isinstance(n, ast.Name)]
        return names

    @staticmethod
    def _placeholder(name):
        # try: name / except NameError: name = __placeholder__("name")
        assign = ast.Assign(
            targets=[ast.Name(name, ast.Store())],
            value=ast.Call(
                func=ast.Name("__placeholder__", ast.Load()),
                args=[ast.Constant(name)],
                keywords=[],
            ),
        )
        return ast.Try(
            body=[ast.Expr(ast.Name(name, ast.Load()))],
            handlers=[ast.ExceptHandler(type=ast.Name("NameError", ast.Load()),
                                        name=None, body=[assign])],
            orelse=[],
            finalbody=[],
        )

    def _wrap(self, statements):
        wrapped = []
        for stmt in statements:
            if isinstance(stmt, (ast.Global, ast.Nonlocal)) or (
                isinstance(stmt, ast.ImportFrom) and stmt.module == "__future__"
            ):
                wrapped.append(stmt)
                continue
            fallback = [self._placeholder(n) for n in self._assigned_names(stmt)]
            handler = ast.ExceptHandler(
                type=ast.Tuple(
                    elts=[ast.Name("Exception", ast.Load()),
                          ast.Name("SystemExit", ast.Load())],
                    ctx=ast.Load(),
                ),
                name=None,
                body=fallback or [ast.Pass()],
            )
            wrapped.append(
                ast.Try(body=[stmt], handlers=[handler], orelse=[], finalbody=[])
            )
        return wrapped

    def generic_visit(self, node):
        super().generic_visit(node)
        if self.wrap:
            for field in ("body", "orelse", "finalbody"):
                value = getattr(node, field, None)
                if isinstance(value, list) and value and isinstance(value[0], ast.stmt):
                    setattr(node, field, self._wrap(value))
        if isinstance(node, (ast.While, ast.For, ast.AsyncFor)):
            guard = ast.Expr(
                ast.Call(
                    func=ast.Name("__loop_guard__", ast.Load()),
                    args=[ast.Constant(id(node))],
                    keywords=[],
                )
            )
            node.body.insert(0, guard)
        return node


def _install_import_hook(sandbox, reprod):
    import importlib.abc
    import importlib.machinery

    class Loader(importlib.machinery.SourceFileLoader):
        def get_code(self, fullname):
            path = self.get_filename(fullname)
            tree = _Resilient(sandbox, wrap=False).visit(
                ast.parse(self.get_data(path), path)
            )
            ast.fix_missing_locations(tree)
            return compile(tree, path, "exec", dont_inherit=True)

    class Finder(importlib.abc.MetaPathFinder):
        def find_spec(self, name, path=None, target=None):
            spec = importlib.machinery.PathFinder.find_spec(name, path)
            if spec and spec.origin and spec.origin.endswith(".py") \
                    and Path(spec.origin).resolve().parent == reprod:
                spec.loader = Loader(name, spec.origin)
            return spec

    sys.meta_path.insert(0, Finder())


def _install_sandbox(sandbox):
    reprod = (sandbox / "repro.d").resolve()
    work = sandbox / "work"
    tmp = sandbox / "tmp"
    captured = tmp / "captured"
    tempfile.tempdir = str(tmp)
    os.environ["TMPDIR"] = str(tmp)
    sys.dont_write_bytecode = True

    stdin_inputs = []

    def capture(data, label):
        if isinstance(data, memoryview):
            data = data.tobytes()
        if not isinstance(data, (bytes, bytearray)) or b"%PDF-" not in data[:1024]:
            return
        label = re.sub(r"[^\w.-]+", "_", re.sub(r"_(pdf|bytes|data)$", "", label))
        captured.mkdir(exist_ok=True)
        path = captured / f"{label or 'captured'}.pdf"
        n = 1
        while path.exists():
            n += 1
            path = captured / f"{label or 'captured'}_{n}.pdf"
        path.write_bytes(data)

    def placeholder(name):
        path = tmp / f"placeholder_{name}"
        path.mkdir(exist_ok=True)
        return str(path)

    def inside_sandbox(path):
        return Path(path).resolve().is_relative_to(sandbox)

    def allowed_command(args, cwd):
        exe = os.path.basename(args[0])
        if exe in ALLOWED_PROGRAMS:
            return args
        if not re.fullmatch(r"python(3(\.\d+)?)?", exe) and args[0] != sys.executable:
            return None
        rest = args[1:]
        while rest and rest[0].startswith("-"):
            if rest[0] in ("-m", "-c"):
                return None
            rest = rest[1:]
        if not rest:
            return None
        script = Path(rest[0])
        if not script.is_absolute():
            script = Path(cwd) / script
        script = script.resolve()
        if script.parent != reprod or script.suffix != ".py":
            return None
        if INFRA_SCRIPT_RE.search(script.name):
            return None
        return [sys.executable, "-E", "-s", "-B", str(script), *rest[1:]]

    real_popen = subprocess.Popen

    class Popen(real_popen):
        def __init__(self, args, *a, **kwargs):
            command = None
            cwd = kwargs.get("cwd") or os.getcwd()
            if not inside_sandbox(cwd):
                cwd = work
            if not kwargs.get("shell") and not isinstance(args, (str, bytes)) and args:
                command = allowed_command([os.fspath(x) for x in args], cwd)
            if command is None:
                raise _Blocked(f"blocked: {args!r}")
            print(f"[allowed] {' '.join(command)}", file=sys.stderr)
            for arg in command[1:]:
                if arg.startswith("/") and inside_sandbox(arg):
                    Path(arg).parent.mkdir(parents=True, exist_ok=True)
            kwargs["cwd"] = str(cwd)
            kwargs.pop("shell", None)
            super().__init__(command, *a, **kwargs)

    subprocess.Popen = Popen
    real_run = subprocess.run

    def run(*args, **kwargs):
        stdin_inputs.append(kwargs.get("input"))
        return real_run(*args, **kwargs)

    subprocess.run = run

    def blocked(*args, **kwargs):
        raise _Blocked(f"blocked: {args!r}")

    for name in (
        "system", "popen", "fork", "forkpty", "posix_spawn", "posix_spawnp",
        "execv", "execve", "execl", "execle", "execlp", "execlpe", "execvp",
        "execvpe", "spawnl", "spawnle", "spawnlp", "spawnlpe", "spawnv",
        "spawnve", "spawnvp", "spawnvpe", "kill", "killpg",
    ):
        if hasattr(os, name):
            setattr(os, name, blocked)

    def keep(*args, **kwargs):
        pass

    shutil.rmtree = keep
    os.remove = keep
    os.unlink = keep
    Path.unlink = keep

    class KeptTemporaryDirectory:
        def __init__(self, suffix=None, prefix=None, dir=None, **kwargs):
            self.name = tempfile.mkdtemp(suffix, prefix, dir)

        def __enter__(self):
            return self.name

        def __exit__(self, *exc):
            return False

        def cleanup(self):
            pass

    tempfile.TemporaryDirectory = KeptTemporaryDirectory
    real_named_temporary_file = tempfile.NamedTemporaryFile

    def named_temporary_file(*args, **kwargs):
        kwargs["delete"] = False
        return real_named_temporary_file(*args, **kwargs)

    tempfile.NamedTemporaryFile = named_temporary_file

    import socket
    import socketserver
    import time
    import urllib.request as request
    import webbrowser

    time.sleep = keep
    socketserver.BaseServer.serve_forever = keep
    request.urlopen = blocked
    socket.create_connection = blocked
    webbrowser.open = keep

    counts = {}

    def loop_guard(key):
        counts[key] = counts.get(key, 0) + 1
        if counts[key] > 1_000_000:
            raise _LoopGuard("loop iteration limit")

    builtins.__loop_guard__ = loop_guard
    builtins.__placeholder__ = placeholder
    _install_import_hook(sandbox, reprod)
    return capture, stdin_inputs


def run_generation_child(sandbox):
    sandbox = Path(sandbox).resolve()
    source = (sandbox / "repro").read_text()
    tree = _Resilient(sandbox).visit(ast.parse(source))
    ast.fix_missing_locations(tree)
    code = compile(tree, str(sandbox / "repro"), "exec")
    capture, stdin_inputs = _install_sandbox(sandbox)
    os.chdir(sandbox / "work")
    sys.argv = [str(sandbox / "repro")]
    namespace = {
        "__name__": "__main__",
        "__file__": str(sandbox / "repro"),
        "__builtins__": builtins,
    }
    try:
        exec(code, namespace)
    finally:
        for name, value in list(namespace.items()):
            if name.startswith("__"):
                continue
            items = [(name, value)]
            if isinstance(value, dict):
                items += [(f"{name}_{k}", v) for k, v in value.items()]
            elif isinstance(value, (list, tuple)):
                items += [(f"{name}_{i}", v) for i, v in enumerate(value)]
            for label, item in items:
                try:
                    capture(item, str(label))
                except Exception:
                    pass
        for item in stdin_inputs:
            try:
                capture(item, "stdin")
            except Exception:
                pass
        sys.stdout.flush()
        sys.stderr.flush()
        os._exit(0)


def generate_pdfs(finding, sandbox, timeout, verbose):
    reprod = finding / "repro.d"
    if reprod.is_dir():
        shutil.copytree(reprod, sandbox / "repro.d",
                        ignore=shutil.ignore_patterns("__pycache__"))
    else:
        (sandbox / "repro.d").mkdir(parents=True)
    shutil.copy(finding / "repro", sandbox / "repro")
    (sandbox / "work").mkdir()
    (sandbox / "tmp").mkdir()
    original_files, seen = set(), set()
    for path in reprod.rglob("*"):
        original_files.add(path.relative_to(finding))
        if path.is_file():
            seen.add(hashlib.sha256(path.read_bytes()).digest())

    run_pdf_generation(sandbox, timeout, verbose)
    return collect_generated_pdfs(sandbox, original_files, seen)


def run_pdf_generation(sandbox, timeout, verbose):
    command = [sys.executable, "-I", "-B", str(Path(__file__).resolve()),
               "--generate-pdfs-in", str(sandbox)]
    child = subprocess.Popen(command, cwd=sandbox / "work", stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True,
                             start_new_session=True)
    try:
        output, _ = child.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        output, _ = child.communicate()
        output = f"(stopped after {timeout} s)\n{output}"
    else:
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    if verbose:
        print(output, file=sys.stderr)


def collect_generated_pdfs(sandbox, original_files, seen):
    """Collect new PDFs in creation order, deduplicating content and names."""
    captured_dir = sandbox / "tmp" / "captured"
    labels, found = {}, []
    candidates = [p for p in sandbox.rglob("*") if p.is_file()]
    for path in sorted(candidates, key=lambda p: (p.stat().st_mtime_ns, str(p))):
        if path.relative_to(sandbox) in original_files:
            continue
        if path.parent == sandbox:
            continue
        try:
            data = read_pdf(path)
        except OSError:
            continue
        if not data:
            continue
        digest = hashlib.sha256(data).digest()
        if path.parent == captured_dir:
            labels.setdefault(digest, path.name)
        if digest in seen:
            continue
        seen.add(digest)
        name = path.name if path.suffix.lower() == ".pdf" else path.name + ".pdf"
        found.append((name, digest, data))

    basenames = Counter(name for name, _, _ in found)
    pdfs, taken = [], set()
    for name, digest, data in found:
        if basenames[name] > 1 and digest in labels:
            name = labels[digest]
        stem, n = name[:-4], 1
        while name in taken:
            n += 1
            name = f"{stem}_{n}.pdf"
        taken.add(name)
        pdfs.append((name, data))
    return pdfs


# --- Attachments ------------------------------------------------------------


def zip_files(files):
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for name, data in files:
            z.writestr(name, data)
    return buffer.getvalue()


def make_attachment(name, summary, data):
    """Prepare an upload, compressing oversized files and enforcing the limit."""
    content_type = content_type_for(name)
    if len(data) > MAX_ATTACHMENT_SIZE and content_type != "application/zip":
        data = zip_files([(name, data)])
        name += ".zip"
        content_type = "application/zip"
    if len(data) > MAX_ATTACHMENT_SIZE:
        print(f"warning: {name} is too large ({len(data)} bytes) and is not attached",
              file=sys.stderr)
        return None
    return {
        "file_name": name,
        "summary": summary if len(summary) <= 250 else summary[:249] + "…",
        "content_type": content_type,
        "data": data,
    }


def collect_attachments(finding, ident, pdfs):
    files = []
    if len(pdfs) > MAX_SEPARATE_PDFS:
        files.append((
            f"{ident}-generated-pdfs.zip",
            "PDFs generated by the reproducer: " + ", ".join(n for n, _ in pdfs),
            zip_files(pdfs),
        ))
    else:
        files.extend((name, f"Test case generated by the reproducer: {name}", data)
                     for name, data in pdfs)

    reproducer = [("repro.py", adapt_attached_file((finding / "repro").read_bytes()))]
    reprod = finding / "repro.d"
    for path in sorted(reprod.rglob("*")):
        if not path.is_file() or "__pycache__" in path.parts:
            continue
        name = path.relative_to(reprod).as_posix()
        data = path.read_bytes()
        if content_type_for(name) == "text/plain":
            data = adapt_attached_file(data)
        reproducer.append((name, data))
    files.append((
        f"{ident}-reproducer.zip",
        "Reproducer: " + ", ".join(n for n, _ in reproducer),
        zip_files(reproducer),
    ))

    attachments = []
    for name, summary, data in files:
        attachment = make_attachment(name, summary, data)
        if attachment is not None:
            attachments.append(attachment)
    return attachments


# --- Bugzilla ---------------------------------------------------------------


class BugzillaError(RuntimeError):
    def __init__(self, message, code):
        super().__init__(message)
        self.code = code


class Bugzilla:
    def __init__(self, url, api_key):
        self.url = url.rstrip("/")
        self.api_key = api_key

    def request(self, method, path, payload=None):
        headers = {
            "Accept": "application/json",
            "User-Agent": "pdfjs-oss-scanner-filer/1.0",
        }
        if self.api_key:
            headers["X-BUGZILLA-API-KEY"] = self.api_key
        data = None
        if payload is not None:
            data = json.dumps(payload).encode()
            headers["Content-Type"] = "application/json"
        req = urllib.request.Request(f"{self.url}/rest/{path}", data=data,
                                     method=method, headers=headers)
        try:
            with urllib.request.urlopen(req, timeout=300) as response:
                return json.load(response)
        except urllib.error.HTTPError as e:
            body = e.read().decode("utf-8", "replace")
            try:
                body = json.loads(body).get("message", body)
            except ValueError:
                pass
            raise BugzillaError(f"Bugzilla {method} {path}: HTTP {e.code}: {body}", e.code)

    def security_group(self, product):
        try:
            result = self.request(
                "GET",
                f"product?names={urllib.parse.quote(product)}"
                "&include_fields=default_security_group",
            )
            group = result["products"][0].get("default_security_group")
        except (RuntimeError, KeyError, IndexError):
            group = None
        return group or FALLBACK_SECURITY_GROUP

    def create_bug(self, payload):
        return self.request("POST", "bug", payload)["id"]

    def ensure_blocks(self, bug_id, blocked_id):
        # Bug creation silently drops dependencies for users without editbugs.
        bug = self.request("GET", f"bug/{bug_id}?include_fields=blocks")["bugs"][0]
        if blocked_id not in bug.get("blocks", []):
            self.request("PUT", f"bug/{bug_id}", {"blocks": {"add": [blocked_id]}})

    def has_attachment(self, bug_id, attachment):
        result = self.request(
            "GET", f"bug/{bug_id}/attachment?include_fields=file_name,size"
        )
        return any(
            a["file_name"] == attachment["file_name"]
            and a["size"] == len(attachment["data"])
            for a in result["bugs"][str(bug_id)]
        )

    def attach_with_retry(self, bug_id, attachment, retries=2):
        # A 5xx from the proxy doesn't say whether the upload went through.
        for attempt in range(retries + 1):
            try:
                return self.attach(bug_id, attachment)
            except BugzillaError as e:
                if e.code < 500 or attempt == retries:
                    raise
                time.sleep(5 * (attempt + 1))
                if self.has_attachment(bug_id, attachment):
                    return None

    def attach(self, bug_id, attachment):
        payload = {
            "ids": [bug_id],
            "file_name": attachment["file_name"],
            "summary": attachment["summary"],
            "content_type": attachment["content_type"],
            "is_patch": False,
            "data": base64.b64encode(attachment["data"]).decode(),
        }
        return self.request("POST", f"bug/{bug_id}/attachment", payload)


def read_token(path):
    path = Path(path).expanduser()
    try:
        lines = path.read_text().splitlines()
    except OSError as e:
        sys.exit(f"Unable to read the Bugzilla API key from {path}: {e}")
    for line in lines:
        line = line.strip()
        if line and not line.startswith("#"):
            return line.split("=", 1)[-1].strip()
    sys.exit(f"No Bugzilla API key in {path}")


def edit_text(text):
    editor = os.environ.get("VISUAL") or os.environ.get("EDITOR") or "vi"
    with tempfile.NamedTemporaryFile("w+", suffix=".md", delete=False) as f:
        f.write(text)
    try:
        subprocess.run([*editor.split(), f.name], check=True)
        return Path(f.name).read_text()
    finally:
        os.unlink(f.name)


def confirm(question):
    try:
        return input(f"{question} [y/N] ").strip().lower() in ("y", "yes")
    except EOFError:
        return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--id", help="finding id, e.g. ANT-2026-DNL1W973 or DNL1W973")
    parser.add_argument("--security", action="store_true",
                        help="file the bug in the product's security group")
    parser.add_argument("--meta-bug", type=int, default=SECURITY_META_BUG,
                        help="meta bug blocked by security bugs (0: none), "
                             f"default: {SECURITY_META_BUG}")
    parser.add_argument("--root", type=Path, default=Path("."),
                        help="directory searched (recursively) for the finding, "
                             "default: the current directory")
    parser.add_argument("--bugzilla-url", default=DEFAULT_BUGZILLA_URL)
    parser.add_argument("--token-file", default=DEFAULT_TOKEN_FILE)
    parser.add_argument("--no-pdf", action="store_true",
                        help="don't run the reproducer to generate the PDFs")
    parser.add_argument("--edit", action="store_true",
                        help="edit the description in $EDITOR before filing")
    parser.add_argument("--dry-run", action="store_true",
                        help="print what would be filed and keep the generated files")
    parser.add_argument("--yes", action="store_true",
                        help="don't ask before filing a security finding publicly")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--generate-pdfs-in", help=argparse.SUPPRESS)
    args = parser.parse_args()

    if args.generate_pdfs_in:
        run_generation_child(args.generate_pdfs_in)
        return
    if not args.id:
        parser.error("--id is required")

    finding = find_finding(args.root, args.id)
    report = (finding / "REPORT.md").read_text()
    ident, title = parse_report(report)
    summary = f"[{ident}] {title}"
    description = build_description(report)
    if args.edit:
        description = edit_text(description)
    if len(description) > MAX_COMMENT_LENGTH:
        sys.exit(f"The description is {len(description)} characters long, "
                 f"Bugzilla accepts at most {MAX_COMMENT_LENGTH}")

    sandbox = Path(tempfile.mkdtemp(prefix=f"bmo-{ident}-"))
    try:
        pdfs = []
        if not args.no_pdf and (finding / "repro").is_file():
            pdfs = generate_pdfs(finding, sandbox / "run", GENERATION_TIMEOUT,
                                 args.verbose)
        attachments = collect_attachments(finding, ident, pdfs)

        if args.dry_run:
            out = sandbox / "attachments"
            out.mkdir()
            for attachment in attachments:
                (out / attachment["file_name"]).write_bytes(attachment["data"])
            (out / "description.md").write_text(description)
            print(f"Summary: {summary}")
            print(f"Product: {PRODUCT} :: {COMPONENT}")
            print(f"Security: {'yes' if args.security else 'no'}")
            if args.security and args.meta_bug:
                print(f"Blocks: {args.meta_bug}")
            print("Attachments:")
            for attachment in attachments:
                print(f"  {attachment['file_name']} ({attachment['content_type']}, "
                      f"{len(attachment['data'])} bytes): {attachment['summary']}")
            print(f"Description and attachments written to {out}")
            print("-" * 78)
            print(description)
            sandbox = None
            return

        if not args.security and finding.parent.name in SECURITY_FOLDERS \
                and not args.yes:
            if not confirm(f"{ident} is a {finding.parent.name} security finding "
                           "and --security was not given: file it publicly?"):
                sys.exit("Aborted")

        bugzilla = Bugzilla(args.bugzilla_url, read_token(args.token_file))
        payload = {
            "product": PRODUCT,
            "component": COMPONENT,
            "summary": summary,
            "version": "unspecified",
            "type": "defect",
            "platform": "Unspecified",
            "op_sys": "Unspecified",
            "description": description,
        }
        if args.security:
            payload["groups"] = [bugzilla.security_group(PRODUCT)]
            if args.meta_bug:
                payload["blocks"] = [args.meta_bug]
        bug_id = bugzilla.create_bug(payload)
        bug_url = f"{bugzilla.url}/show_bug.cgi?id={bug_id}"
        print(f"Filed {bug_url}")
        if "blocks" in payload:
            try:
                bugzilla.ensure_blocks(bug_id, args.meta_bug)
                print(f"  blocks bug {args.meta_bug}")
            except RuntimeError as e:
                print(f"  FAILED to make it block bug {args.meta_bug}: {e}",
                      file=sys.stderr)

        failures = 0
        for attachment in attachments:
            try:
                bugzilla.attach_with_retry(bug_id, attachment)
                print(f"  attached {attachment['file_name']}")
            except RuntimeError as e:
                failures += 1
                print(f"  FAILED to attach {attachment['file_name']}: {e}",
                      file=sys.stderr)
        if failures:
            sys.exit(f"{failures} attachment(s) could not be added to {bug_url}")
    finally:
        if sandbox:
            shutil.rmtree(sandbox, ignore_errors=True)


if __name__ == "__main__":
    main()
