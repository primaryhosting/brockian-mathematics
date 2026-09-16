"""Lean file layout lint — two evidence-boundary checks, stdlib only.

1. Import placement. Lean 4 accepts `import` only in the file header: after nothing
   but whitespace and ordinary comments. Four modules in the 14 September full-corpus
   job fail on exactly this ("invalid 'import' command, it must be used in the
   beginning of the file"). This check reproduces Lean's rule without Lean.

2. Attestation form. `engine.verify.normalize` hoists and dedupes imports before
   hashing, so a stored attestation covers the *normalized* text. If the file on disk
   is not already in that form, the attested artifact and the committed artifact are
   different byte strings. This check reports whether they coincide.

Note: `engine.verify.normalize` is not idempotent (it inserts a separator line on
every pass). `normalize_v2` below is the idempotent form. It is NOT substituted for the
legacy function — every existing content hash depends on the legacy behaviour — but
it is what a file must equal to be "in attestation form".

Usage:  python3 scripts/lean_layout_lint.py [--fix] FILE...
Exit status 1 if any file has a misplaced import.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))
from engine import verify  # noqa: E402


def normalize_v2(content: str) -> str:
    """Idempotent attestation form: deduped imports, one blank line, body without
    leading blank lines. normalize_v2(normalize_v2(x)) == normalize_v2(x)."""
    imports, body = [], []
    for line in content.splitlines():
        s = line.strip()
        if s.startswith("import "):
            if s not in imports:
                imports.append(s)
        else:
            body.append(line)
    while body and not body[0].strip():
        body.pop(0)
    out = imports + ([""] if imports and body else []) + body
    text = "\n".join(out)
    return text + ("\n" if content.endswith("\n") else "")


def content_lines(text: str) -> list[bool]:
    """For each line, True if it carries Lean content (not blank, not inside an
    ordinary comment). Doc comments `/--` and module docs `/-!` are commands, so they
    count as content; ordinary `/- ... -/` (nesting) and `-- ...` do not."""
    flags = []
    depth = 0          # nesting depth of ordinary block comments
    for line in text.splitlines():
        i, n, has_content = 0, len(line), False
        while i < n:
            if depth:
                if line.startswith("-/", i):
                    depth -= 1; i += 2
                elif line.startswith("/-", i) and not line.startswith("/--", i) \
                        and not line.startswith("/-!", i):
                    depth += 1; i += 2
                else:
                    i += 1
                continue
            if line.startswith("--", i):
                break
            if line.startswith("/-", i) and not line.startswith("/--", i) \
                    and not line.startswith("/-!", i):
                depth += 1; i += 2
                continue
            if not line[i].isspace():
                has_content = True
            i += 1
        flags.append(has_content)
    return flags


def check(text: str) -> dict:
    lines = text.splitlines()
    flags = content_lines(text)
    imports, misplaced, seen_other = [], [], False
    for no, (line, is_content) in enumerate(zip(lines, flags), start=1):
        if not is_content:
            continue
        if line.lstrip().startswith("import ") or line.strip() == "import":
            imports.append(no)
            if seen_other:
                misplaced.append(no)
        else:
            seen_other = True
    stripped = [lines[no - 1].strip() for no in imports]
    dupes = sorted({s for s in stripped if stripped.count(s) > 1})
    return {"imports": imports, "misplaced_imports": misplaced, "duplicate_imports": dupes,
            "import_placement_ok": not misplaced,
            "attestation_form": normalize_v2(text) == text,
            "legacy_normalize_changes_file": verify.normalize(text) != text}


def fix(text: str) -> str:
    return normalize_v2(text)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("files", nargs="+", type=pathlib.Path)
    ap.add_argument("--fix", action="store_true", help="rewrite files into attestation form")
    args = ap.parse_args(argv)
    report, bad = {}, False
    for path in args.files:
        text = path.read_text()
        result = check(text)
        if args.fix and (result["misplaced_imports"] or not result["attestation_form"]):
            fixed = fix(text)
            path.write_text(fixed)
            result["fixed"] = True
            result["after"] = check(fixed)
        report[str(path)] = result
        bad |= bool(result["misplaced_imports"]) and not args.fix
    print(json.dumps(report, indent=2))
    return int(bad)


if __name__ == "__main__":
    sys.exit(main())
