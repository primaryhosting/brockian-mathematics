#!/usr/bin/env python3
"""export_obsidian.py — registry/theorems.json → Obsidian knowledge-graph notes.

Writes markdown notes into the Obsidian vault at OBSIDIAN_VAULT (default
/Volumes/BCC-Storage/knowledge/brockian-math), under wiki/registry/:

  wiki/registry/index.md            — honest registry counts + verification
                                      posture (AXLE-attested vs lake_build
                                      pending — stated, never conflated)
  wiki/registry/modules/<Module>.md — ONE note per module that contains at
                                      least one PROVED theorem. Frontmatter:
                                      status/register tallies/attestation
                                      date; body: statement summary, theorem
                                      list, [[wikilinks]] to dependency
                                      modules (parsed from the module's Lean
                                      imports) and to the existing vault
                                      concept notes.
  wiki/log.md                       — append-only run line (only when notes
                                      actually changed)

TRUTH: every number in every note is read from registry/theorems.json and
registry/attestations/* — nothing is fabricated. The registry says
lake_build is "pending" for these entries; the notes SAY so ("AXLE-attested;
lake_build pending"), and never claim "proven by lake build".

IDEMPOTENT: a content-hash manifest (wiki/registry/.export_manifest.json)
skips unchanged notes, so a re-run against an unchanged registry writes
nothing and appends nothing to the log.

NEVER A BLOCKER: the vault lives on a slow USB APFS volume that sometimes
stalls. Every vault operation is wrapped; a missing/unmounted vault is an
honest SKIP (exit 0), a wall-clock budget (OBSIDIAN_EXPORT_BUDGET, default
300s) stops a slow run early with an honest partial report, and the conveyor
invokes this script as a subprocess with its own timeout, recorded but never
fatal to the cycle.
"""
from __future__ import annotations

import argparse
import datetime
import glob
import hashlib
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)

DEFAULT_VAULT = os.environ.get(
    "OBSIDIAN_VAULT", "/Volumes/BCC-Storage/knowledge/brockian-math")
DEFAULT_REGISTRY = os.path.join(REPO, "registry", "theorems.json")
DEFAULT_ATTEST_DIR = os.path.join(REPO, "registry", "attestations")

MANIFEST_NAME = ".export_manifest.json"
IMPORT_RE = re.compile(r"^import\s+(Brockian\.[A-Za-z0-9_.]+)\s*$", re.M)

# Deterministic keyword → existing vault concept note (wiki/concepts/*.md).
# Only notes that already exist in the vault are mapped; nothing is invented.
CONCEPT_KEYWORDS = [
    ("pentagonal", "pentagonal-law"),
    ("partition", "partition-theory"),
    ("spectral", "spectral-invariants"),
    ("costrace", "spectral-invariants"),
]
CONCEPT_ALWAYS = "lean4-formalization"  # every note describes a Lean 4 module


def _now_date() -> str:
    return datetime.date.today().isoformat()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


# ---------------------------------------------------------------- repo reads

def load_registry(path: str) -> dict:
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


def attestation_dates(attest_dir: str) -> dict:
    """module name → ISO date of its attestation file (file mtime — the
    registry attestations carry no in-band date; the frontmatter labels the
    source honestly as attestation_date_source: file-mtime)."""
    out = {}
    for path in sorted(glob.glob(os.path.join(attest_dir, "*.json"))):
        try:
            with open(path, encoding="utf-8") as fh:
                mod = json.load(fh).get("module")
            if mod:
                mtime = os.path.getmtime(path)
                out[mod] = datetime.date.fromtimestamp(mtime).isoformat()
        except Exception:  # noqa: BLE001 — one bad file never kills the export
            continue
    return out


def module_imports(src_root: str, source_file: str) -> list:
    """Brockian.* imports of one module's Lean source (dependency wikilinks).
    A missing/unreadable source file yields no links — never an error."""
    if not source_file:
        return []
    try:
        with open(os.path.join(src_root, source_file), encoding="utf-8") as fh:
            return IMPORT_RE.findall(fh.read())
    except Exception:  # noqa: BLE001
        return []


def group_modules(registry: dict) -> dict:
    """module → list of its registry entries, for modules with ≥1 PROVED."""
    by_mod = {}
    for t in registry.get("theorems") or []:
        mod = t.get("module")
        if mod:
            by_mod.setdefault(mod, []).append(t)
    return {m: ts for m, ts in by_mod.items()
            if any(t.get("register") == "PROVED" for t in ts)}


# ---------------------------------------------------------------- note bodies

def _posture(entries: list) -> dict:
    """Honest verification tally for one module's entries."""
    axle_verified = sum(
        1 for t in entries
        if ((t.get("verification") or {}).get("axle") or {}).get("verdict")
        == "verified")
    lake_built = sum(
        1 for t in entries
        if (t.get("verification") or {}).get("lake_build") == "verified")
    lake_pending = sum(
        1 for t in entries
        if (t.get("verification") or {}).get("lake_build") == "pending")
    return {"axle_verified": axle_verified, "lake_built": lake_built,
            "lake_pending": lake_pending}


def _summary_text(entries: list) -> str:
    """Statement summary: the first non-empty statement, else the first
    provenance note — always real registry text, truncated, never invented."""
    for t in entries:
        s = (t.get("statement") or "").strip()
        if s:
            return s[:600]
    for t in entries:
        s = (t.get("provenance_note") or "").strip()
        if s:
            return s[:600]
    return ("No statement text captured in the registry for this module "
            "(see the Lean source for the statements).")


def concept_links(module: str, entries: list) -> list:
    hay = (module + " " + " ".join(
        (t.get("provenance_note") or "") for t in entries)).lower()
    out = [CONCEPT_ALWAYS]
    for kw, note in CONCEPT_KEYWORDS:
        if kw in hay and note not in out:
            out.append(note)
    return out


def build_module_note(module: str, entries: list, attest_date,
                      imports: list) -> str:
    regs = {}
    for t in entries:
        r = t.get("register") or "UNKNOWN"
        regs[r] = regs.get(r, 0) + 1
    post = _posture(entries)
    envs = sorted({
        ((t.get("verification") or {}).get("axle") or {}).get("environment")
        for t in entries} - {None})
    fm = [
        "---",
        f"module: {module}",
        "status: PROVED",
        "register_counts: " + json.dumps(regs, sort_keys=True),
        f"attestation_date: {attest_date or 'unknown'}",
        "attestation_date_source: "
        + ("registry/attestations file mtime" if attest_date else "none"),
        f"axle_verified: {post['axle_verified']}",
        f"lake_built: {post['lake_built']}",
        f"lake_build_pending: {post['lake_pending']}",
        "generated_by: scripts/export_obsidian.py",
        "---",
    ]
    proved = [t for t in entries if t.get("register") == "PROVED"]
    body = [
        "",
        f"# {module}",
        "",
        f"**Verification posture (honest):** {post['axle_verified']} of "
        f"{len(entries)} declarations AXLE-attested"
        + (f" ({', '.join(envs)})" if envs else "")
        + f"; lake_build verified for {post['lake_built']}, pending for "
        f"{post['lake_pending']}. AXLE-attested is NOT the same as "
        "lake-built — pending entries await the local lake_build leg.",
        "",
        "## Summary",
        "",
        _summary_text(entries),
        "",
        f"## Theorems ({len(proved)} PROVED of {len(entries)} entries)",
        "",
    ]
    for t in sorted(entries, key=lambda x: x.get("name") or ""):
        line = f"- `{t.get('name')}` — {t.get('kind')}, {t.get('register')}"
        stmt = (t.get("statement") or "").strip()
        if stmt:
            line += f": {stmt[:200]}"
        body.append(line)
    deps = sorted(set(imports) - {module})
    body += ["", "## Dependencies", ""]
    if deps:
        body += [f"- [[{d}]]" for d in deps]
    else:
        body.append("- (no Brockian imports found in the module source)")
    body += ["", "## Concepts", ""]
    body += [f"- [[{c}]]" for c in concept_links(module, entries)]
    body.append("")
    return "\n".join(fm + body)


def build_index_note(registry: dict, modules: dict) -> str:
    summary = registry.get("summary") or {}
    theorems = registry.get("theorems") or []
    lake = {}
    axle_ok = 0
    for t in theorems:
        v = t.get("verification") or {}
        lb = v.get("lake_build") or "unknown"
        lake[lb] = lake.get(lb, 0) + 1
        if (v.get("axle") or {}).get("verdict") == "verified":
            axle_ok += 1
    lines = [
        "---",
        "title: Brockian Registry — Knowledge Graph Index",
        f"generated: {_now_date()}",
        "generated_by: scripts/export_obsidian.py",
        "---",
        "",
        "# Brockian Registry Index",
        "",
        "Generated from `registry/theorems.json` (the repo's registry of "
        "record). Counts below are read from the registry — never edited "
        "by hand, never estimated.",
        "",
        "## Honest counts",
        "",
        f"- Registry entries: **{len(theorems)}**",
    ]
    for k in sorted(summary):
        lines.append(f"- {k}: **{summary[k]}**")
    lines += [
        "",
        "## Verification posture — stated plainly",
        "",
        f"- AXLE-attested declarations: **{axle_ok}** of {len(theorems)}",
    ]
    for k in sorted(lake):
        lines.append(f"- lake_build {k}: **{lake[k]}**")
    lines += [
        "",
        "**Posture:** PROVED in this registry means the declaration is "
        "AXLE-attested (independent Lean environment check). The local "
        "`lake build` leg is a separate, pending attestation for the "
        "entries marked lake_build pending above — those results are NOT "
        "lake-built yet, and no note in this vault claims otherwise.",
        "",
        f"## Modules with PROVED theorems ({len(modules)})",
        "",
    ]
    for m in sorted(modules):
        lines.append(f"- [[{m}]]")
    lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------- vault writes

def _atomic_write(path: str, content: str) -> None:
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        fh.write(content)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def export(registry_path=None, vault=None, attest_dir=None, src_root=None,
           budget=None, now_date=None) -> dict:
    """Run one export. Returns an honest result dict; raises only on a broken
    REGISTRY (repo side) — every vault-side failure is caught and reported."""
    vault = vault or DEFAULT_VAULT
    budget = float(budget if budget is not None
                   else os.environ.get("OBSIDIAN_EXPORT_BUDGET", "300"))
    deadline = time.monotonic() + budget
    result = {"status": "ok", "written": 0, "unchanged": 0, "errors": 0,
              "remaining": 0, "skipped_reason": None, "log_appended": False}

    if not os.path.isdir(vault):
        result.update(status="skipped",
                      skipped_reason=f"vault not mounted: {vault}")
        return result

    registry = load_registry(registry_path or DEFAULT_REGISTRY)
    modules = group_modules(registry)
    attest = attestation_dates(attest_dir or DEFAULT_ATTEST_DIR)

    reg_dir = os.path.join(vault, "wiki", "registry")
    mod_dir = os.path.join(reg_dir, "modules")
    manifest_path = os.path.join(reg_dir, MANIFEST_NAME)
    try:
        os.makedirs(mod_dir, exist_ok=True)
    except Exception as e:  # noqa: BLE001 — vault stall/unmount mid-run
        result.update(status="skipped", skipped_reason=f"vault mkdir: {e}")
        return result

    manifest = {}
    try:
        with open(manifest_path, encoding="utf-8") as fh:
            manifest = json.load(fh)
        if not isinstance(manifest, dict):
            manifest = {}
    except Exception:  # noqa: BLE001 — missing/corrupt manifest = full write
        manifest = {}

    # index first (cheap), then per-module notes; content-hash skip on both.
    notes = {"index.md": build_index_note(registry, modules)}
    for mod in sorted(modules):
        entries = modules[mod]
        src = (entries[0].get("source") or {}).get("file")
        notes[os.path.join("modules", f"{mod}.md")] = build_module_note(
            mod, entries, attest.get(mod),
            module_imports(src_root or REPO, src))

    new_manifest = {}
    pending = list(notes.items())
    for i, (rel, content) in enumerate(pending):
        if time.monotonic() > deadline:
            result.update(status="partial", remaining=len(pending) - i)
            # not-reached notes KEEP their old hash: a next run recomputes
            # and rewrites only if the content actually differs, so a
            # budget-cut run never degrades idempotency for the rest.
            for rest_rel, _ in pending[i:]:
                if rest_rel in manifest:
                    new_manifest[rest_rel] = manifest[rest_rel]
            break
        digest = sha256_text(content)
        if manifest.get(rel) == digest:
            new_manifest[rel] = digest
            result["unchanged"] += 1
            continue
        try:
            _atomic_write(os.path.join(reg_dir, rel), content)
            new_manifest[rel] = digest
            result["written"] += 1
        except Exception:  # noqa: BLE001 — vault hiccup on one file
            result["errors"] += 1

    # manifest: written/unchanged notes only (a failed write is retried next
    # run because its hash is absent). Prunes notes for modules gone from the
    # registry so their next appearance rewrites cleanly.
    try:
        _atomic_write(manifest_path,
                      json.dumps(new_manifest, indent=1, sort_keys=True))
    except Exception:  # noqa: BLE001
        result["errors"] += 1

    if result["written"] or result["errors"]:
        line = (
            f"\n## {now_date or _now_date()}\n\n"
            f"- Registry knowledge-graph export: {result['written']} note(s) "
            f"written, {result['unchanged']} unchanged, "
            f"{result['errors']} error(s), {result['remaining']} not reached "
            f"(budget). PROVED modules: {len(modules)}; posture: "
            f"AXLE-attested, lake_build pending entries stated as pending.\n")
        try:
            with open(os.path.join(vault, "wiki", "log.md"), "a",
                      encoding="utf-8") as fh:
                fh.write(line)
            result["log_appended"] = True
        except Exception:  # noqa: BLE001
            result["errors"] += 1
    return result


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--registry", default=None)
    p.add_argument("--vault", default=None)
    p.add_argument("--attest-dir", default=None)
    p.add_argument("--src-root", default=None,
                   help="root containing Brockian/*.lean for dependency links")
    p.add_argument("--budget", type=float, default=None)
    args = p.parse_args(argv)
    try:
        res = export(registry_path=args.registry, vault=args.vault,
                     attest_dir=args.attest_dir, src_root=args.src_root,
                     budget=args.budget)
    except Exception as e:  # noqa: BLE001 — repo-side failure: report, rc=1
        print(f"export_obsidian: error {e}")
        return 1
    print("export_obsidian: "
          + " ".join(f"{k}={res[k]}" for k in
                     ("status", "written", "unchanged", "errors",
                      "remaining", "skipped_reason")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
