#!/usr/bin/env python3
"""Self-contained harvest + gate path (wave 54).

Owns the whole route from an Aristotle pid to a registered theorem WITHOUT
importing any previous wave module: three waves in a row died on one-line
type bugs inside the inherited wave25/27/28 helper chain, and the promised
verbatim AXLE error dump was never delivered because it lived in a lane that
was patched away.

Pipeline per candidate (fail-closed at every step):

  download+flatten ALL .lean files from the returned project
    -> normalize the def-spec entries (bare name | (path,name) | [path,name])
    -> faithfulness screens on the PRE-dedup artifact text
         * verbatim corpus-def anchor
         * strict same-name-different-statement shadow screen
         * reconstruction-phrase scan
         * pure-alias / thin-Mathlib-wrapper screen
    -> append-only splice into the target's own corpus module, carrying the
       `open` / `open scoped` scope lines the declaration needs
    -> isolated per-candidate AXLE attestation (scratch copy)
    -> on failure: dump AXLE's verbatim Lean errors to the log AND to
       review/<short>/NOTES.md, restore the module, reject.

Nothing here edits registry/theorems.json; registration goes through
scripts/gen_registry.py under the caller's monotonic guard.
"""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import traceback

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.environ.get("AUTOLAB_DATA_DIR") or os.path.join(ROOT, ".autolab-data")
STATE = os.path.join(DATA, "aristotle_state.json")
HARVEST = os.path.join(DATA, "harvest")
REVIEW = os.path.join(ROOT, "review")
T0 = time.time()

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|instance)\s+([A-Za-z_][^\s:({\[]*)",
    re.MULTILINE,
)
RECONSTRUCT_RE = re.compile(r"reconstruct|restated|reproduced[^\n]{0,40}not (?:part of|supplied)", re.I)


def log(msg: str) -> None:
    print(f"[{time.time() - T0:7.1f}s] {msg}", flush=True)


def sh(cmd, timeout=300):
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, cwd=ROOT)
        return p.returncode, (p.stdout or "") + (p.stderr or "")
    except subprocess.TimeoutExpired:
        return -9, f"timeout after {timeout}s"
    except Exception as exc:  # pragma: no cover - defensive
        return -1, f"{type(exc).__name__}: {exc}"


# ---------------------------------------------------------------- state ----
def load_state() -> dict:
    if os.path.exists(STATE):
        with open(STATE) as fh:
            return json.load(fh)
    return {}


def save_state(st: dict) -> None:
    os.makedirs(DATA, exist_ok=True)
    tmp = STATE + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(st, fh, indent=1)
    os.replace(tmp, STATE)


def norm_defs(spec: dict) -> list[tuple[str, str]]:
    """Coerce every def-spec entry to (path, name) exactly once.

    Historic states store bare names, tuples and JSON lists interchangeably;
    passing a list where a name was expected is what crashed waves 49/52/53.
    """
    out: list[tuple[str, str]] = []
    default = spec.get("file", "")
    for entry in spec.get("defs", []) or []:
        if isinstance(entry, (list, tuple)):
            if len(entry) >= 2:
                path, name = str(entry[0]), str(entry[1])
            else:
                path, name = default, str(entry[0])
        else:
            path, name = default, str(entry)
        assert isinstance(path, str) and isinstance(name, str), (path, name)
        out.append((path, name))
    return out


# ------------------------------------------------------------- lean bits ---
def norm(text: str) -> str:
    return re.sub(r"\s+", " ", text or "").strip()


def decls(src: str) -> list[dict]:
    """All top-level declarations with their full block text."""
    hits = list(DECL_RE.finditer(src))

    def _adjusted(m):
        """Declaration start, including an immediately preceding doc comment."""
        start = m.start()
        doc = src.rfind("/--", 0, start)
        if doc != -1 and src.find("-/", doc) < start and not src[src.find("-/", doc) + 2:start].strip():
            start = doc
        return start

    starts = [_adjusted(m) for m in hits]
    out = []
    for i, m in enumerate(hits):
        start = starts[i]
        # a block ends where the NEXT declaration begins, doc comment included:
        # using the raw keyword position dragged the next decl's doc comment into
        # this block, which produced false 'def deviates from corpus' rejects and
        # orphaned doc comments after dedup (waves 54-56).
        end = starts[i + 1] if i + 1 < len(hits) else len(src)
        for stop in ("\nend ", "\nnamespace ", "\nsection", "\n@[simp"):
            k = src.find(stop, m.end())
            if k != -1 and k < end:
                end = k
        out.append({"kind": m.group(1), "name": m.group(2), "block": src[start:end].rstrip() + "\n",
                    "start": start})
    return out


def strip_comments(text: str) -> str:
    """Drop `/-- ... -/` doc comments, `/- ... -/` blocks and `--` line comments.

    Wave 54 lost 9 faithful candidates because a declaration block carries its
    doc comment, so the doc text was compared as part of the statement.
    """
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            i = j
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def statement_of(block: str) -> str:
    """Signature text of a declaration block (everything before the proof)."""
    body = strip_comments(block)
    k = re.search(r"\b(theorem|lemma|def|abbrev|instance)\b", body)
    if k:
        body = body[k.start():]
    for cut in (":= by", ":=\n", ":= ", "\n  by", " by\n"):
        k = body.find(cut)
        if k != -1:
            body = body[:k]
    return norm(body)


def block_of(src: str, name: str) -> str | None:
    for d in decls(src):
        if d["name"] == name or d["name"].endswith("." + name):
            return d["block"]
    return None


def scope_lines(src: str, upto: int) -> list[str]:
    """`open` / `open scoped` lines in effect above position `upto`."""
    out = []
    for m in re.finditer(r"^(open scoped [^\n]+|open [^\n]+)$", src[:upto], re.MULTILINE):
        line = m.group(1).strip()
        if line.endswith(" in"):
            continue
        out.append(line)
    return out


def ensure_scope(path: str, lines: list[str]) -> int:
    """Additively, idempotently ensure each scope line exists in a module."""
    src = open(os.path.join(ROOT, path)).read()
    missing = [l for l in lines if not re.search(rf"^{re.escape(l)}\s*$", src, re.MULTILINE)]
    if not missing:
        return 0
    imports = list(re.finditer(r"^import [^\n]+$", src, re.MULTILINE))
    at = imports[-1].end() if imports else 0
    new = src[:at] + "\n" + "\n".join(missing) + src[at:]
    open(os.path.join(ROOT, path), "w").write(new)
    log(f"  scope carry: added {missing}")
    return len(missing)


# --------------------------------------------------------------- harvest ---
def fetch(short: str, pid: str) -> str | None:
    """Download + flatten every .lean file of the returned project."""
    d = os.path.join(HARVEST, short)
    flat = os.path.join(d, "FLAT.lean")
    if os.path.exists(flat) and f"theorem {short}" in open(flat).read():
        return flat
    os.makedirs(d, exist_ok=True)
    tgz = os.path.join(d, "out.tar.gz")
    if not os.path.exists(tgz):
        rc, out = sh(["uvx", "--from", "aristotlelib@latest", "aristotle",
                      "download", pid, "--destination", tgz], timeout=300)
        if rc != 0 or not os.path.exists(tgz):
            log(f"fetch {short}: not terminal / download failed rc={rc}: {out[-160:]}")
            return None
    try:
        with tarfile.open(tgz, "r:gz") as t:
            t.extractall(d)
    except Exception as exc:
        log(f"fetch {short}: bad tarball {exc}")
        return None
    files = []
    for root, _, names in os.walk(d):
        for f in names:
            if f.endswith(".lean") and f != "FLAT.lean":
                files.append(os.path.join(root, f))
    if not files:
        log(f"fetch {short}: no .lean in project")
        return None
    # main file last so its declarations win; inline internal project imports
    files.sort(key=lambda p: (f"theorem {short}" in open(p, errors="replace").read(), len(p)))
    parts, seen = [], set()
    for p in files:
        src = open(p, errors="replace").read()
        src = re.sub(r"^import RequestProject[^\n]*$", "", src, flags=re.MULTILINE)
        for line in re.findall(r"^import [^\n]+$", src, re.MULTILINE):
            seen.add(line.strip())
        src = re.sub(r"^import [^\n]+$", "", src, flags=re.MULTILINE)
        parts.append(f"-- >>> {os.path.relpath(p, d)}\n{src}")
    text = "\n".join(sorted(seen)) + "\n" + "\n".join(parts)
    open(flat, "w").write(text)
    log(f"fetch {short}: flattened {len(files)} file(s), {len(text)} bytes")
    return flat if f"theorem {short}" in text else None


# --------------------------------------------------------------- screens ---
def screen(short: str, target: str, art_src: str, spec: dict, goal: str) -> tuple[str | None, str]:
    """Faithfulness screens on the PRE-dedup artifact. Returns (reason, ok)."""
    tgt = block_of(art_src, short)
    if tgt is None:
        return "target theorem not found in artifact", ""
    if goal:
        if statement_of(tgt) != statement_of(goal.split(":=")[0]):
            g, p = statement_of(goal.split(":=")[0]), statement_of(tgt)
            if g.replace("theorem " + short, "").strip() != p.replace("theorem " + short, "").strip():
                return f"faithfulness mismatch\n  proved: {p}\n  goal:   {g}", ""
    corpus_defs = norm_defs(spec)
    anchored = 0
    for path, name in corpus_defs:
        cpath = os.path.join(ROOT, path)
        if not os.path.exists(cpath):
            continue
        cblock = block_of(open(cpath).read(), name)
        ablock = block_of(art_src, name)
        if cblock is None or ablock is None:
            continue
        if norm(strip_comments(cblock)) == norm(strip_comments(ablock)):
            anchored += 1
        else:
            # binder normalisation: the corpus may take binders from a section `variable`
            a = re.sub(r"[{\[(][^)}\]]*[)}\]]", "", norm(strip_comments(ablock)))
            c = re.sub(r"[{\[(][^)}\]]*[)}\]]", "", norm(strip_comments(cblock)))
            if a == c:
                anchored += 1
            else:
                return f"def {name} deviates from corpus (shadow risk)", ""
    if RECONSTRUCT_RE.search(art_src) and anchored == 0:
        return "artifact claims reconstruction and anchors no corpus def", ""
    if re.fullmatch(r"theorem[^:]*:.*:=\s*[A-Za-z_][\w.]*(\s+[\w.()]+)*\s*", norm(tgt)) and \
            len(norm(tgt).split(":=")[-1].split()) <= 3:
        return "thin wrapper / alias (single-term proof)", ""
    return None, tgt


# ------------------------------------------------------------- attestation --
ATT_DIR = os.path.join(ROOT, "registry", "attestations")


def _verified(path: str) -> set[str]:
    try:
        rep = json.load(open(path))
    except Exception:
        return set()
    return {d.get("name", "") for d in rep.get("declarations", [])
            if d.get("axle_verdict") == "verified"
            and d.get("axioms_ok") is True
            and isinstance(d.get("axioms"), list)
            and d.get("verification_quarantine") is not True}


def _evidence_ok(declaration: dict) -> bool:
    """Whether one fresh declaration carries promotion-grade evidence."""
    if declaration.get("axle_verdict") != "verified":
        return False
    if declaration.get("axioms_ok") is not True:
        return False
    if declaration.get("verification_quarantine") is True:
        return False
    if declaration.get("kind", "theorem") in ("theorem", "lemma"):
        return isinstance(declaration.get("axioms"), list)
    return True


def merge_attestation_reports(old: dict | None, fresh: dict) -> dict:
    """Merge a fresh partial AXLE report without dropping sibling evidence.

    ``scripts/attest.py`` intentionally reports only the declarations requested
    on its command line.  Its CLI writes that partial report to the canonical
    module receipt, so blindly accepting the file erases every sibling.  Wave 66
    exposed exactly that failure.  This function treats declaration FQNs as keys,
    replaces only declarations present in ``fresh``, and carries the fresh module
    verdict/content hash over the complete sibling set.

    Quarantine metadata on untouched siblings is preserved byte-for-byte.  A
    quarantined declaration is cleared only when it is itself present in a fresh,
    promotion-grade report.
    """
    if fresh.get("module_verified") is not True:
        raise ValueError("fresh attestation did not verify the module")
    module = fresh.get("module")
    if not module:
        raise ValueError("fresh attestation has no module")
    if not fresh.get("content_hash"):
        raise ValueError("fresh attestation has no content_hash")

    fresh_decls = fresh.get("declarations")
    if not isinstance(fresh_decls, list) or not fresh_decls:
        raise ValueError("fresh attestation has no declarations")
    fresh_by_name: dict[str, dict] = {}
    for declaration in fresh_decls:
        name = declaration.get("name")
        if not name or name in fresh_by_name:
            raise ValueError(f"fresh attestation has invalid/duplicate name: {name!r}")
        if not _evidence_ok(declaration):
            raise ValueError(f"fresh declaration lacks clean evidence: {name}")
        fresh_by_name[name] = declaration

    if old is None:
        return fresh
    if old.get("module") != module:
        raise ValueError(f"module mismatch: {old.get('module')} != {module}")
    old_decls = old.get("declarations")
    if not isinstance(old_decls, list):
        raise ValueError("old attestation declarations are malformed")

    old_names: set[str] = set()
    merged_decls: list[dict] = []
    for declaration in old_decls:
        name = declaration.get("name")
        if not name or name in old_names:
            raise ValueError(f"old attestation has invalid/duplicate name: {name!r}")
        old_names.add(name)
        merged_decls.append(fresh_by_name.pop(name, declaration))
    for declaration in fresh_decls:
        if declaration.get("name") in fresh_by_name:
            merged_decls.append(declaration)
            fresh_by_name.pop(declaration["name"])

    merged = dict(old)
    for key in ("module", "environment", "module_verified", "content_hash"):
        merged[key] = fresh.get(key)
    merged["declarations"] = merged_decls
    merged_names = {d.get("name") for d in merged_decls}
    if not old_names <= merged_names or len(merged_decls) < len(old_decls):
        raise ValueError("attestation merge violated sibling non-regression")
    return merged


def atomic_json_write(path: str, payload: dict) -> None:
    """Durably replace one JSON file without exposing a partial receipt."""
    directory = os.path.dirname(path)
    os.makedirs(directory, exist_ok=True)
    tmp = ""
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=directory,
            prefix=os.path.basename(path) + ".", suffix=".tmp", delete=False,
        ) as fh:
            tmp = fh.name
            json.dump(payload, fh, indent=2)
            fh.write("\n")
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(tmp, path)
        tmp = ""
        dir_fd = os.open(directory, os.O_RDONLY)
        try:
            os.fsync(dir_fd)
        finally:
            os.close(dir_fd)
    finally:
        if tmp and os.path.exists(tmp):
            os.remove(tmp)


def att_snapshot() -> dict[str, bytes]:
    """Bytes of every canonical attestation file (cheap: a few hundred KB)."""
    snap: dict[str, bytes] = {}
    if os.path.isdir(ATT_DIR):
        for name in sorted(os.listdir(ATT_DIR)):
            if name.endswith(".json"):
                p = os.path.join(ATT_DIR, name)
                snap[p] = open(p, "rb").read()
    return snap


def att_guard(snap: dict[str, bytes], short: str = "") -> int:
    """Restore any canonical attestation that lost verified declarations.

    scripts/attest.py always writes registry/attestations/<Module>.json, which is
    what scripts/gen_registry.py reads. Wave 54 let a *rejected* candidate's
    all-failed scratch report land there and the derived registry shrank by 42
    entries. A canonical report may only be replaced by a SUPERSET; otherwise the
    old bytes are restored and the new report is parked under review/<short>/.
    """
    reverted = 0
    for p, old in snap.items():
        if not os.path.exists(p):
            open(p, "wb").write(old)
            reverted += 1
            log(f"ATT GUARD: restored deleted {os.path.basename(p)}")
            continue
        new_bytes = open(p, "rb").read()
        if new_bytes == old:
            continue
        tmp = p + ".old"
        open(tmp, "wb").write(old)
        new_ok, old_ok = _verified(p), _verified(tmp)
        if not new_ok >= old_ok:
            if short:
                d = os.path.join(REVIEW, short)
                os.makedirs(d, exist_ok=True)
                shutil.copy(p, os.path.join(d, "attestation-scratch-" + os.path.basename(p)))
            open(p, "wb").write(old)
            reverted += 1
            log(f"ATT GUARD: {os.path.basename(p)} would lose verified decls "
                f"({len(old_ok)} -> {len(new_ok)}); restored canonical report")
        os.remove(tmp)
    # brand-new module files are fine (nothing to lose), keep them
    return reverted


def attest(path: str, module: str, names: list[str], short: str = "") -> tuple[bool, dict, str]:
    """Attest requested names in-process, then atomically merge the receipt.

    Calling ``scripts/attest.py`` as a CLI is forbidden here: its CLI owns the
    canonical output path and therefore exposes a crash window in which a partial
    one-declaration report replaces a complete module receipt.  The library API
    returns the report without writing; only this sibling-preserving code commits
    it.
    """
    snap = att_snapshot()
    rep: dict = {}
    try:
        import attest as attest_module  # local scripts/attest.py
        rep = attest_module.attest(path, module, sorted(names), attest_module.DEFAULT_ENV)
        rc = 0 if attest_module.attestation_complete(rep) else 1
        out = json.dumps(rep, indent=2)
    except Exception as exc:  # pragma: no cover - network/service defensive path
        rc = -1
        out = f"{type(exc).__name__}: {exc}"
    requested = {f"{module}.{name}" for name in names}
    returned = {d.get("name"): d for d in rep.get("declarations", [])}
    ok = (
        rc == 0
        and rep.get("module_verified") is True
        and requested == set(returned)
        and all(_evidence_ok(returned[name]) for name in requested)
    )

    canonical = os.path.join(ATT_DIR, os.path.splitext(os.path.basename(path))[0] + ".json")
    if ok:
        old = json.loads(snap[canonical]) if canonical in snap else None
        try:
            merged = merge_attestation_reports(old, rep)
            atomic_json_write(canonical, merged)
            rep = merged
        except Exception as exc:
            ok = False
            log(f"attest {module}: sibling-preserving merge failed: {exc}")

    if not ok:
        # Preserve the failed/partial report for diagnosis, then restore every
        # canonical receipt byte-for-byte.  A brand-new failed receipt is removed.
        if short and os.path.exists(canonical):
            d = os.path.join(REVIEW, short)
            os.makedirs(d, exist_ok=True)
            scratch = os.path.join(d, "attestation-scratch-" + os.path.basename(canonical))
            atomic_json_write(scratch, rep or {"error": out})
        for receipt, old_bytes in snap.items():
            if not os.path.exists(receipt) or open(receipt, "rb").read() != old_bytes:
                with open(receipt, "wb") as fh:
                    fh.write(old_bytes)
        if canonical not in snap and os.path.exists(canonical):
            os.remove(canonical)
    else:
        old_count = len(json.loads(snap[canonical]).get("declarations", [])) if canonical in snap else 0
        log(f"attest {module}: merged receipt {old_count} -> {len(rep['declarations'])} declarations")
    return ok, rep, out


def dump_errors(short: str, path: str) -> int:
    """Verbatim AXLE Lean errors -> log + review/<short>/NOTES.md. Never optional."""
    rc, out = sh([sys.executable, "scripts/axle_client.py", path], timeout=600)
    text = out[:4096]
    log(f"  AXLE VERBATIM ERRORS for {short} (rc={rc}):\n{text}")
    d = os.path.join(REVIEW, short)
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, "NOTES.md"), "a") as fh:
        fh.write(f"\n\n## wave54 verbatim AXLE errors (rc={rc})\n```\n{text}\n```\n")
    return 1


# ------------------------------------------------------------------ gate ---
def gate(target: str, pid: str, spec: dict, goal: str, counters: dict) -> bool:
    """Full atomic gate for one candidate. True == spliced and attested."""
    short = target.split(".")[-1]
    art = fetch(short, pid)
    if not art:
        return False
    art_src = open(art).read()
    reason, tgt_block = screen(short, target, art_src, spec, goal)
    if reason:
        log(f"REJECT {short}: {reason}")
        counters["rejected_screen"] += 1
        return False
    path = spec.get("file")
    module = spec.get("module")
    if not path or not module:
        log(f"REJECT {short}: no target spec")
        return False
    full = os.path.join(ROOT, path)
    backup = open(full).read()
    if re.search(rf"^\s*(?:theorem|lemma)\s+{re.escape(short)}\b", backup, re.MULTILINE):
        log(f"skip {short}: already present in {path}")
        return False
    # helpers the artifact needs: everything the corpus does not already have
    corpus_names = {d["name"] for d in decls(backup)}
    extra = []
    tgt_pos = art_src.find(tgt_block[:40])
    for d in decls(art_src):
        if d["start"] >= tgt_pos or d["name"] == short:
            continue
        if d["name"] in corpus_names:
            counters["dropped_corpus_identical"] += 1
            continue
        if d["kind"] in ("def", "abbrev", "instance"):
            continue
        extra.append(d)
    counters["scope_lines_added"] += ensure_scope(path, scope_lines(art_src, tgt_pos))
    body = "\n\n".join([d["block"] for d in extra] + [tgt_block])
    src = open(full).read()
    ns = f"namespace {module}"
    if ns in src and f"\nend {module}" in src:
        at = src.rindex(f"\nend {module}")
        new = src[:at] + "\n\n" + body + src[at:]
    else:
        new = src.rstrip() + "\n\n" + body
    open(full, "w").write(new)
    names = [short] + [d["name"] for d in extra]
    ok, rep, raw = attest(path, module, names, short)
    if ok:
        log(f"ACCEPT {short}: attested in isolation ({len(extra)} helper(s))")
        counters["attested"] += 1
        return True
    log(f"ATOMIC REJECT {short}: isolated attestation failed")
    for d in rep.get("declarations", []):
        if d.get("axle_verdict") != "verified" or not d.get("axioms_ok"):
            log(f"    {d.get('name')}: verdict={d.get('axle_verdict')} axioms={d.get('axioms')}")
    counters["axle_reports_dumped"] += dump_errors(short, path)
    counters["axle_failures"] += 1
    open(full, "w").write(backup)
    d = os.path.join(REVIEW, short)
    os.makedirs(d, exist_ok=True)
    shutil.copy(art, os.path.join(d, "FLAT.lean"))
    return False


def self_test() -> bool:
    """Exercise the pure path over cached artifacts before the real work."""
    assert norm_defs({"file": "f.lean", "defs": ["a", ("p", "b"), ["q", "c"]]}) == [
        ("f.lean", "a"), ("p", "b"), ("q", "c")]
    src = "import Mathlib\nopen Finset\nopen scoped BigOperators\n\ntheorem foo (n : Nat) : n = n := by rfl\n"
    d = decls(src)
    assert [x["name"] for x in d] == ["foo"], d
    assert statement_of(d[0]["block"]).startswith("theorem foo")
    assert "open scoped BigOperators" in scope_lines(src, len(src))
    log("self-test: ok")
    return True


if __name__ == "__main__":
    try:
        self_test()
    except Exception:
        traceback.print_exc()
        sys.exit(1)
