#!/usr/bin/env python3
"""List imports and top-level declarations for upstream-candidate Lean files.

This is intentionally read-only and stdlib-only. It does not parse Lean fully;
it extracts enough structure for Mathlib PR planning:

  - `import ...` lines
  - top-level `namespace ...` lines
  - top-level declaration headers beginning with theorem/lemma/def/etc.

Pass file paths as arguments. With no arguments it scans the current upstream
candidate source set.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


DEFAULT_FILES = [
    "Brockian/WeylOperator.lean",
    "Brockian/WeylCayley.lean",
    "Brockian/WeylClosure.lean",
    "Brockian/WeylEssSelfAdjoint.lean",
    "Brockian/WeylFreeLaplacian2.lean",
    "Brockian/SingularSeries.lean",
    "Brockian/SingularSeriesConvergence.lean",
    "Brockian/Admissibility.lean",
    "Brockian/AdmissibilityCRT.lean",
    "Brockian/Sieve.lean",
    "Brockian/Automorphism.lean",
    "Brockian/AutomorphismFull.lean",
    "Brockian/D5Representation.lean",
    "Brockian/D5Isotypic.lean",
    "Brockian/D5FourierInversion.lean",
    "Brockian/D5LaplacianModes.lean",
    "Brockian/Spectral.lean",
    "Brockian/CycleSpectrumFamily.lean",
    "Brockian/C5SpectralMultiplicities.lean",
]

DECL_RE = re.compile(
    r"^(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive)\s+"
    r"(?P<name>[A-Za-z0-9_'.]+)"
)


def blank_block_comments(text: str) -> str:
    """Blank Lean block comments, preserving line numbers."""
    out = list(text)
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out[i] = " "
            out[i + 1] = " "
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            out[i] = " "
            out[i + 1] = " "
            i += 2
            continue
        if depth and text[i] != "\n":
            out[i] = " "
        i += 1
    return "".join(out)


def strip_line_comment(line: str) -> str:
    idx = line.find("--")
    return line if idx < 0 else line[:idx]


def scan(path: Path) -> tuple[list[tuple[int, str]], list[tuple[int, str]], list[tuple[int, str, str]]]:
    text = blank_block_comments(path.read_text(encoding="utf-8"))
    imports: list[tuple[int, str]] = []
    namespaces: list[tuple[int, str]] = []
    decls: list[tuple[int, str, str]] = []
    for lineno, raw in enumerate(text.splitlines(), start=1):
        line = strip_line_comment(raw).strip()
        if not line:
            continue
        if line.startswith("import "):
            imports.append((lineno, line.removeprefix("import ").strip()))
            continue
        if line.startswith("namespace "):
            namespaces.append((lineno, line.removeprefix("namespace ").strip()))
            continue
        match = DECL_RE.match(line)
        if match:
            decls.append((lineno, match.group("kind"), match.group("name")))
    return imports, namespaces, decls


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", default=DEFAULT_FILES)
    parser.add_argument("--names-only", action="store_true")
    args = parser.parse_args()

    for raw in args.files:
        path = Path(raw)
        if not path.exists():
            print(f"{raw}: MISSING")
            continue
        imports, namespaces, decls = scan(path)
        if args.names_only:
            for _lineno, _kind, name in decls:
                print(name)
            continue
        print(f"## {path}")
        print("imports:")
        for lineno, name in imports:
            print(f"  {lineno}: {name}")
        print("namespaces:")
        for lineno, name in namespaces:
            print(f"  {lineno}: {name}")
        print("declarations:")
        for lineno, kind, name in decls:
            print(f"  {lineno}: {kind} {name}")
        print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
