"""Discover and de-duplicate Lean source files across the scattered Brockian corpus.

Emits a manifest keyed by md5 so byte-identical duplicates (the ledger recorded many)
collapse to one entry. Output feeds the ingest/triage pipeline (spec 3.1).

Usage:
    python3 scripts/ingest_discover.py <dir-or-file> [<dir-or-file> ...] -o _ingest/manifest.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from dataclasses import asdict, dataclass


@dataclass
class Source:
    md5: str
    size: int
    paths: list[str]  # every on-disk location with this exact content


def _md5(path: str) -> str:
    h = hashlib.md5()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def discover(roots: list[str]) -> list[Source]:
    """Return unique Lean sources (keyed by md5) found under the given roots.

    Skips Mathlib/.lake/toolchain vendored trees so only Brockian-authored files
    are ingested.
    """
    by_md5: dict[str, Source] = {}
    # Directory names that are vendored toolchains / deps / caches — never Brockian-authored.
    prune_dirs = {
        ".lake", ".elan", ".elan_local", ".git", ".Trash", ".cache", "build",
        ".venv", ".venv-leandojo", ".leandojo_brockian_lean_repo", "lean_leandojo_repo",
        "LeanDojo", "leandojo_traces", "lean_traced", "llmstep-upstream",
        "toolchains", "node_modules", "__pycache__",
    }
    # Path substrings that also mark vendored trees (belt and suspenders).
    skip_markers = (os.sep + "src" + os.sep + "lean" + os.sep, os.sep + "mathlib" + os.sep,
                    os.sep + ".lake" + os.sep, os.sep + "toolchains" + os.sep)
    # Vendored dependency library roots (Mathlib deps) by top-level module dir name.
    dep_libs = {"Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Cli", "Init",
                "Std", "Lean", "LeanSearchClient", "ImportGraph", "Plausible", "Lake"}
    for root in roots:
        if os.path.isfile(root) and root.endswith(".lean"):
            files = [root]
        else:
            files = []
            for dirpath, dirs, names in os.walk(root):
                # prune vendored / dependency directories in place
                dirs[:] = [d for d in dirs if d not in prune_dirs and d not in dep_libs]
                for n in names:
                    if n.endswith(".lean"):
                        files.append(os.path.join(dirpath, n))
        for path in files:
            ap = os.path.abspath(path)
            if any(m in ap for m in skip_markers):
                continue
            try:
                digest = _md5(ap)
                size = os.path.getsize(ap)
            except OSError:
                continue
            if digest in by_md5:
                if ap not in by_md5[digest].paths:
                    by_md5[digest].paths.append(ap)
            else:
                by_md5[digest] = Source(md5=digest, size=size, paths=[ap])
    return sorted(by_md5.values(), key=lambda s: (-s.size, s.md5))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("roots", nargs="+")
    ap.add_argument("-o", "--out", default="_ingest/manifest.json")
    args = ap.parse_args()
    sources = discover(args.roots)
    os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
    with open(args.out, "w") as f:
        json.dump({"count": len(sources), "sources": [asdict(s) for s in sources]}, f, indent=2)
    dup = sum(len(s.paths) - 1 for s in sources)
    print(f"{len(sources)} unique Lean sources ({dup} duplicate copies collapsed) -> {args.out}")


if __name__ == "__main__":
    main()
