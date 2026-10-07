#!/usr/bin/env python3
"""Compute transitive import closure of Lean modules within the OAI library,
and scan the closure for trust-relevant tokens.

Usage: python3 -I scripts/audit_external_lean_closure.py <lean_root> <module> [<module> ...]

Static pre-check for an EXTERNAL Lean library before its theorems are imported into the
Brockian corpus (used for openai/math family 003, 2026-10-07).  Walks the transitive
import closure under <lean_root>, lists external packages touched, and scans for the
tokens that would break a zero-sorry / standard-axioms claim.  It is a necessary
pre-condition, NOT a kernel check: the kernel check is `lake build` + `#print axioms`.
"""
import os
import re
import sys
from collections import deque

LEAN_ROOT = sys.argv[1]
ROOTS = sys.argv[2:]

IMPORT_RE = re.compile(r'^\s*import\s+(\S+)', re.M)

# Tokens that affect trust. Each is (label, regex, severity).
# Severity: 'fatal' = breaks zero-sorry/axiom-clean claim if present;
#           'review' = legitimate but worth human eyes.
TOKENS = [
    ("sorry",          re.compile(r'\bsorry\b'),                    "fatal"),
    ("admit",          re.compile(r'\badmit\b'),                    "fatal"),
    ("axiom",          re.compile(r'^\s*(?:@\[.*\]\s*)?axiom\b', re.M), "fatal"),
    ("unsafe",         re.compile(r'\bunsafe\b'),                   "fatal"),
    ("implemented_by", re.compile(r'implemented_by'),               "fatal"),
    ("extern",         re.compile(r'@\[extern'),                    "fatal"),
    ("native_decide",  re.compile(r'\bnative_decide\b'),            "review"),
    ("opaque",         re.compile(r'^\s*opaque\b', re.M),           "review"),
    ("partial_def",    re.compile(r'\bpartial\s+def\b'),            "review"),
    ("set_option_maxHeartbeats_0", re.compile(r'maxHeartbeats\s+0\b'), "review"),
    ("decide",         re.compile(r'\bdecide\b'),                   "info"),
    ("noncomputable",  re.compile(r'\bnoncomputable\b'),            "info"),
]


def module_to_path(mod: str):
    p = os.path.join(LEAN_ROOT, *mod.split('.')) + '.lean'
    return p if os.path.isfile(p) else None


def imports_of(path: str):
    with open(path, encoding='utf-8', errors='replace') as fh:
        text = fh.read()
    # Only scan the header: imports must precede any other command.
    # Take everything up to the first line that is not blank/comment/import.
    header = []
    in_block_comment = False
    for line in text.splitlines():
        s = line.strip()
        if in_block_comment:
            if '-/' in s:
                in_block_comment = False
            continue
        if s.startswith('/-'):
            if '-/' not in s:
                in_block_comment = True
            continue
        if not s or s.startswith('--') or s.startswith('import'):
            header.append(line)
            continue
        break
    return IMPORT_RE.findall('\n'.join(header)), text


def main():
    seen_internal = {}
    external = {}
    queue = deque(ROOTS)
    while queue:
        mod = queue.popleft()
        if mod in seen_internal or mod in external:
            continue
        path = module_to_path(mod)
        if path is None:
            external[mod] = external.get(mod, 0) + 1
            continue
        imps, text = imports_of(path)
        seen_internal[mod] = (path, text)
        for i in imps:
            if i not in seen_internal and i not in external:
                queue.append(i)

    total_lines = 0
    hits = {label: [] for label, _, _ in TOKENS}
    for mod, (path, text) in seen_internal.items():
        total_lines += text.count('\n') + 1
        # strip comments for token scan: line comments and block comments
        stripped = re.sub(r'/-.*?-/', '', text, flags=re.S)
        stripped = re.sub(r'--[^\n]*', '', stripped)
        for label, rx, sev in TOKENS:
            for m in rx.finditer(stripped):
                lineno = stripped.count('\n', 0, m.start()) + 1
                hits[label].append((mod, lineno))

    print(f"ROOTS: {ROOTS}")
    print(f"internal modules in closure: {len(seen_internal)}")
    print(f"total lines (internal):      {total_lines}")
    print()
    ext_pkgs = {}
    for e in external:
        top = e.split('.')[0]
        ext_pkgs[top] = ext_pkgs.get(top, 0) + 1
    print("external packages referenced (top-level namespace: #modules):")
    for k, v in sorted(ext_pkgs.items(), key=lambda kv: -kv[1]):
        print(f"  {k}: {v}")
    print()
    print("token scan (comments stripped):")
    for label, rx, sev in TOKENS:
        h = hits[label]
        print(f"  [{sev:6}] {label:28} {len(h):6}")
    print()
    for label, rx, sev in TOKENS:
        if sev in ("fatal", "review") and hits[label]:
            print(f"--- {label} locations (first 40) ---")
            for mod, ln in hits[label][:40]:
                print(f"  {mod}:{ln}")
            if len(hits[label]) > 40:
                print(f"  ... and {len(hits[label]) - 40} more")
            print()

    # emit module list for later use
    out = os.environ.get("CLOSURE_OUT")
    if out:
        with open(out, 'w') as fh:
            for mod in sorted(seen_internal):
                fh.write(mod + '\n')
        print(f"module list written to {out}")


if __name__ == '__main__':
    main()
