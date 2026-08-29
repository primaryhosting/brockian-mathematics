#!/usr/bin/env python3
"""Kernel-check Lean modules and their local imports in dependency order.

Lean resolves project imports from compiled ``.olean`` files; invoking ``lean`` on an
arbitrary changed file in a clean checkout therefore fails when a local dependency has
not been compiled yet.  This helper discovers the transitive ``Brockian.*`` import DAG
and invokes Lean once per source file, in topological order.  It deliberately avoids a
whole-project ``lake build`` so promotion checks remain bounded and diagnosable.
"""
from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path


LOCAL_IMPORT = re.compile(r"^\s*import\s+(Brockian(?:\.[A-Za-z0-9_']+)+)\s*(?:--.*)?$")


def module_path(module: str, root: Path) -> Path:
    """Return the source path for a dotted local module name."""
    return root / (module.replace(".", "/") + ".lean")


def local_imports(source: Path, root: Path) -> list[Path]:
    """Read local imports, failing closed when a Brockian module is absent."""
    imports: list[Path] = []
    for line in source.read_text(encoding="utf-8").splitlines():
        match = LOCAL_IMPORT.match(line)
        if not match:
            continue
        dependency = module_path(match.group(1), root)
        if not dependency.is_file():
            raise FileNotFoundError(
                f"{source.relative_to(root)} imports missing local module "
                f"{match.group(1)} ({dependency.relative_to(root)})"
            )
        imports.append(dependency)
    return imports


def dependency_order(sources: list[Path], root: Path) -> list[Path]:
    """Return a stable topological order for sources and local dependencies."""
    root = root.resolve()
    ordered: list[Path] = []
    complete: set[Path] = set()
    active: list[Path] = []

    def visit(source: Path) -> None:
        source = source.resolve()
        if source in complete:
            return
        if source in active:
            cycle = active[active.index(source):] + [source]
            names = " -> ".join(str(path.relative_to(root)) for path in cycle)
            raise ValueError(f"local Lean import cycle: {names}")
        if not source.is_file():
            raise FileNotFoundError(f"Lean source does not exist: {source}")
        if not source.is_relative_to(root):
            raise ValueError(f"Lean source is outside repository root: {source}")

        active.append(source)
        for dependency in local_imports(source, root):
            visit(dependency)
        active.pop()
        complete.add(source)
        ordered.append(source)

    for source in sources:
        visit(source)
    return ordered


def check_modules(sources: list[Path], root: Path) -> None:
    """Compile each source to the normal Lake output tree, one file at a time."""
    root = root.resolve()
    for source in dependency_order(sources, root):
        relative = source.relative_to(root)
        output = root / ".lake" / "build" / "lib" / "lean" / relative.with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        command = ["lake", "env", "lean", "-o", str(output), str(relative)]
        print("+ " + " ".join(command), flush=True)
        subprocess.run(command, cwd=root, check=True)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Kernel-check Lean files after compiling local imports in DAG order."
    )
    parser.add_argument("sources", nargs="+", type=Path)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    args = parser.parse_args()

    root = args.root.resolve()
    sources = [path if path.is_absolute() else root / path for path in args.sources]
    check_modules(sources, root)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
