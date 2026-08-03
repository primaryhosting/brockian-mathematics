#!/usr/bin/env python3
"""Generate docs/PROGRAM-REPORT.md from registry/theorems.json (SSOT).

Counts are never invented: they are read from the live registry summary (or
recomputed by counting `theorems[].register`). Flagship samples are selected
by name/module patterns only when present in the registry.

Usage:
  python3 scripts/gen_program_report.py
  python3 scripts/gen_program_report.py --registry registry/theorems.json --out docs/PROGRAM-REPORT.md
"""
from __future__ import annotations

import argparse
import json
import subprocess
from collections import Counter
from datetime import date
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_REGISTRY = ROOT / "registry" / "theorems.json"
DEFAULT_OUT = ROOT / "docs" / "PROGRAM-REPORT.md"

REGISTER_ORDER = ("PROVED", "DEFINITION", "CONDITIONAL", "DISCHARGED", "CONJECTURE")

FLAGSHIP_PATTERNS: list[tuple[str, list[str], str]] = [
    (
        "Euler pentagonal number theorem (unconditional close)",
        ["FranklinFixedPoint.pentagonalNumberTheorem"],
        "Franklin fixed-point path; prior conditional forms reclassified DISCHARGED.",
    ),
    (
        "Why five / golden rigidity",
        ["GaloisWhyFive.why_five", "GaloisWhyFive.quadratic_iff_five", "GaloisWhyFive.degree_five"],
        "Quadratic degree for cos-generator iff p = 5; degree formulas for 3/5/7.",
    ),
    (
        "Admissibility q−ν law",
        [
            "Admissibility.universal_admissibility_count",
            "Admissibility.admissibility_count_five",
            "Admissibility.admissibility_count_three",
        ],
        "Exact start-residue counts mod q; twin (mod 3) and Brockian (mod 5) cases.",
    ),
    (
        "Aut(C₅) ≅ D₅",
        ["Automorphism.Full.aut_equiv_dihedral", "Automorphism.Full.aut_card_eq_ten"],
        "Faithful dihedral action upgraded to full automorphism isomorphism.",
    ),
    (
        "Algebraic connectivity / golden spectrum on C₅",
        [
            "Connectivity.pentagon_lambda2_phi",
            "ConnectivityGoldenBridge.algebraic_connectivity_C5",
            "C5SpectralMultiplicities.golden_unique_to_five_setlevel",
        ],
        "Laplacian gap and golden eigenvalue membership unique at five.",
    ),
    (
        "ξ functional equation & zero reflection (scaffold)",
        [
            "XiFunctionalEquation.riemannXi_functional_equation",
            "RiemannXiSymmetry.riemannXi_eq_zero_iff_reflect",
            "RiemannScaffold.riemannXi_eq_zero_of_nontrivial_zeta_zero",
        ],
        "Scaffolding for Hilbert–Pólya-style attack; RH itself remains CONDITIONAL/open.",
    ),
    (
        "Local Goldbach / singular series kernel",
        [
            "Goldbach.CovarianceScaffold.singular_series_finite_goldbachPairTuple_pos_of_even",
            "SingularSeries.localFactorAt_eq",
        ],
        "Local kernels proved; global Goldbach transfer is CONJECTURE, not PROVED.",
    ),
]

NON_CLAIMS = [
    (
        "Riemann Hypothesis",
        "RH_of_BrockianSystem",
        "Scaffolded as CONDITIONAL on a named BrockianSystem hypothesis; not shut.",
    ),
    (
        "Global Goldbach transfer",
        "GoldbachComb.GoldbachCovarianceTransfer",
        "Named CONJECTURE (Prop container); local covariance is PROVED separately.",
    ),
    (
        "Unbounded Kato / full Schrödinger ESA",
        "KatoUnbounded.essentiallySelfAdjoint_perturb",
        "Bounded / free-model packages PROVED; full unbounded ESA remains CONDITIONAL.",
    ),
    (
        "Free Laplacian ESA via Plancherel (full link)",
        "FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel",
        "Plancherel infrastructure partially closed; full free −Δ ESA via Fourier still CONDITIONAL.",
    ),
    (
        "Global equidistribution / BV transfer",
        "EquidistributionBVReduction.configCount_density_of_BV",
        "Reduction lemmas present; density/BV uniformity steps stay CONDITIONAL.",
    ),
]


def git_tip(repo: Path) -> dict[str, str]:
    out: dict[str, str] = {
        "full": "unknown",
        "short": "unknown",
        "subject": "unknown",
        "date": "unknown",
    }
    try:
        full = subprocess.check_output(
            ["git", "-C", str(repo), "rev-parse", "HEAD"], text=True
        ).strip()
        short = subprocess.check_output(
            ["git", "-C", str(repo), "rev-parse", "--short", "HEAD"], text=True
        ).strip()
        subject = subprocess.check_output(
            ["git", "-C", str(repo), "log", "-1", "--format=%s"], text=True
        ).strip()
        gdate = subprocess.check_output(
            ["git", "-C", str(repo), "log", "-1", "--format=%ci"], text=True
        ).strip()
        out.update(full=full, short=short, subject=subject, date=gdate)
    except (subprocess.CalledProcessError, FileNotFoundError, OSError):
        pass
    return out


def load_registry(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as f:
        return json.load(f)


def count_registers(theorems: list[dict[str, Any]]) -> dict[str, int]:
    c: Counter[str] = Counter()
    for t in theorems:
        reg = t.get("register")
        if reg:
            c[str(reg)] += 1
    return dict(c)


def find_name(theorems: list[dict[str, Any]], needle: str) -> dict[str, Any] | None:
    """Match full name or trailing segment (module-qualified or bare)."""
    for t in theorems:
        name = t.get("name") or ""
        if name == needle or name.endswith("." + needle) or needle in name:
            # Prefer exact endswith for multi-segment needles
            if name.endswith(needle) or name == needle:
                return t
    for t in theorems:
        name = t.get("name") or ""
        if needle in name:
            return t
    return None


def verification_stats(theorems: list[dict[str, Any]]) -> dict[str, Any]:
    envs: Counter[str] = Counter()
    verdicts: Counter[str] = Counter()
    lake: Counter[str] = Counter()
    axioms_ok = 0
    for t in theorems:
        v = t.get("verification") or {}
        axle = v.get("axle") or {}
        envs[str(axle.get("environment") or "missing")] += 1
        verdicts[str(axle.get("verdict") or "missing")] += 1
        lake[str(v.get("lake_build") or "missing")] += 1
        if v.get("axioms_ok") is True:
            axioms_ok += 1
    return {
        "envs": dict(envs),
        "verdicts": dict(verdicts),
        "lake": dict(lake),
        "axioms_ok": axioms_ok,
        "n": len(theorems),
    }


def module_count(theorems: list[dict[str, Any]]) -> int:
    return len({t.get("module") for t in theorems if t.get("module")})


def attestation_count(repo: Path) -> int:
    att = repo / "registry" / "attestations"
    if not att.is_dir():
        return 0
    return sum(1 for p in att.iterdir() if p.suffix == ".json")


def certificate_names(repo: Path) -> list[str]:
    cert = repo / "registry" / "certificates"
    if not cert.is_dir():
        return []
    return sorted(p.stem for p in cert.iterdir() if p.suffix == ".json")


def render_report(
    registry: dict[str, Any],
    tip: dict[str, str],
    registry_path: Path,
    n_attestations: int,
    certs: list[str],
) -> str:
    theorems: list[dict[str, Any]] = list(registry.get("theorems") or [])
    summary_file = dict(registry.get("summary") or {})
    summary_count = count_registers(theorems)
    # Prefer file summary when present; fall back to recount; assert match when both exist.
    summary = summary_file if summary_file else summary_count
    if summary_file and summary_count:
        for k, v in summary_count.items():
            if summary_file.get(k) != v:
                # Recount wins if mismatch (report truth from list).
                summary = summary_count
                break

    def n(reg: str) -> int:
        return int(summary.get(reg, 0))

    proved = n("PROVED")
    definition = n("DEFINITION")
    conditional = n("CONDITIONAL")
    discharged = n("DISCHARGED")
    conjecture = n("CONJECTURE")
    total_decl = len(theorems)
    n_modules = module_count(theorems)
    vstats = verification_stats(theorems)
    gen_from = registry.get("generated_from") or "registry"
    report_date = date.today().isoformat()

    # Register table rows
    reg_rows = []
    for reg in REGISTER_ORDER:
        if reg in summary:
            reg_rows.append(f"| **{reg}** | {summary[reg]} |")
    for reg, cnt in sorted(summary.items()):
        if reg not in REGISTER_ORDER:
            reg_rows.append(f"| **{reg}** | {cnt} |")

    # Flagship bullets
    flagship_lines: list[str] = []
    for title, needles, blurb in FLAGSHIP_PATTERNS:
        hits: list[str] = []
        for needle in needles:
            t = find_name(theorems, needle)
            if t and t.get("register") in ("PROVED", "DISCHARGED"):
                hits.append(f"`{t['name']}` **[{t['register']}]**")
        if hits:
            flagship_lines.append(f"- **{title}.** {blurb}")
            for h in hits[:4]:
                flagship_lines.append(f"  - {h}")
        else:
            # Still list pattern only if any related name exists
            related = [
                t
                for t in theorems
                if any(n.split(".")[-1].lower() in (t.get("name") or "").lower() for n in needles)
            ]
            if related:
                flagship_lines.append(
                    f"- **{title}.** {blurb} (see registry modules matching pattern)."
                )

    # Theme rough clusters (informational only)
    themes: Counter[str] = Counter()
    for t in theorems:
        m = t.get("module") or ""
        if "Weyl" in m:
            themes["Weyl / spectral / operator"] += 1
        elif "Goldbach" in m or "Singular" in m:
            themes["Goldbach / singular series"] += 1
        elif "Admiss" in m or "Sieve" in m or "Twin" in m:
            themes["Admissibility / sieve"] += 1
        elif any(x in m for x in ("Franklin", "Pentagonal", "Partition", "Ramanujan")):
            themes["Pentagonal / Franklin / partition"] += 1
        elif any(x in m for x in ("Galois", "Cos", "Cyclotomic")):
            themes["Galois / cyclotomic / cos-trace"] += 1
        elif any(
            x in m
            for x in (
                "D5",
                "C5",
                "Automorphism",
                "Connectivity",
                "Spectral",
                "Pentagon",
                "Affine",
            )
        ):
            themes["D₅ / C₅ spectral & symmetry"] += 1
        elif "Riemann" in m or "Xi" in m:
            themes["Riemann / ξ scaffold"] += 1
        elif any(x in m for x in ("Metallic", "Golden", "Core")):
            themes["Core / metallic / golden"] += 1
        elif "Penrose" in m:
            themes["Penrose"] += 1
        elif "Equidistribution" in m:
            themes["Equidistribution"] += 1
        else:
            themes["Other"] += 1
    theme_rows = "\n".join(f"| {k} | {v} |" for k, v in themes.most_common())

    non_claim_lines: list[str] = []
    for label, needle, note in NON_CLAIMS:
        t = find_name(theorems, needle)
        if t:
            non_claim_lines.append(
                f"| **{label}** | `{t['name']}` | **{t.get('register')}** | {note} |"
            )
        else:
            non_claim_lines.append(
                f"| **{label}** | *(pattern `{needle}`)* | see registry | {note} |"
            )

    # CONDITIONAL full list (compact)
    cond_lines = []
    for t in theorems:
        if t.get("register") == "CONDITIONAL":
            cond_lines.append(f"| `{t.get('name')}` | `{t.get('module')}` |")

    disc_lines = []
    for t in theorems:
        if t.get("register") == "DISCHARGED":
            disc_lines.append(f"| `{t.get('name')}` | `{t.get('module')}` |")

    conj_lines = []
    for t in theorems:
        if t.get("register") == "CONJECTURE":
            conj_lines.append(f"| `{t.get('name')}` | `{t.get('module')}` |")

    lake_pending = vstats["lake"].get("pending", 0)
    axle_verified = vstats["verdicts"].get("verified", 0)
    env_main = max(vstats["envs"].items(), key=lambda kv: kv[1])[0] if vstats["envs"] else "unknown"
    cert_txt = ", ".join(f"`{c}`" for c in certs) if certs else "*(none yet)*"

    body = f"""# Brockian Verified Core — Program Report

**Audience:** technical partners, advisors, scientific collaborators
**Classification:** Partner-facing (non-confidential). Counts pinned to the live registry.
**Report generated:** {report_date}
**Tip commit:** `{tip['full']}` (`{tip['short']}`) — *{tip['subject']}* ({tip['date']})
**Registry source:** `{registry_path.as_posix() if registry_path.is_absolute() else registry_path}`
**Generated from:** {gen_from}

> **Brand sentence:** *We ship what is proven and mark what is not.*

Regenerate this document anytime:

```bash
python3 scripts/gen_program_report.py
```

Partner strategy context (do not confuse with this ledger snapshot):
[`docs/partner/2026-08-02-verified-intelligence-strategy-brief.md`](partner/2026-08-02-verified-intelligence-strategy-brief.md)

---

## 1. Executive summary

The **Brockian Verified Core** is a Lean 4 + Mathlib formalization program with a
hard honesty firewall: a declaration is **PROVED** only when it is sorry-free,
uses only standard axioms, and carries an independent **AXLE** verification
verdict at a pinned environment. Registers are **derived** by
`scripts/gen_registry.py` — never hand-painted.

| Snapshot | Value |
|----------|------:|
| **PROVED** | **{proved}** |
| **DEFINITION** | **{definition}** |
| **CONDITIONAL** | **{conditional}** |
| **DISCHARGED** | **{discharged}** |
| **CONJECTURE** | **{conjecture}** |
| Declarations in registry | {total_decl} |
| Modules with entries | {n_modules} |
| Module attestation files | {n_attestations} |
| Certificate factory units | {len(certs)} ({cert_txt}) |
| AXLE environment | `{env_main}` |
| AXLE verdict = verified | {axle_verified} / {vstats['n']} |
| Local `lake_build` field | **{lake_pending} pending** (see §6 caveats) |

**What closed (reference process wins):** Euler’s pentagonal number theorem
unconditionally in-core; Galois / “why five” degree rigidity; the q−ν
admissibility law; D₅ / C₅ spectral structure; large local Goldbach and
singular-series kernels.

**What stays open (explicit non-claims):** Riemann Hypothesis, global Goldbach
transfer, full unbounded essentially-self-adjoint packages — scaffolded or
conditional, **not** counted as PROVED.

---

## 2. Register table (source of truth)

Registers are derived from axioms + AXLE verdict + provenance rung
(DISCHARGED = former CONDITIONAL whose hypothesis was later proved in-core).

| Register | Count |
|----------|------:|
{chr(10).join(reg_rows)}

| Meaning | Gate |
|---------|------|
| **PROVED** | Sorry-free; axioms ⊆ `{{propext, Classical.choice, Quot.sound}}`; no `native_decide`; **AXLE verified** at named env |
| **DEFINITION** | Supporting `def` / structure (not a theorem claim) |
| **CONDITIONAL** | Depends on a named hypothesis (`conditional_rung` set) |
| **DISCHARGED** | Former CONDITIONAL closed by a later in-core PROVED result |
| **CONJECTURE** | Named Prop container — never typed as an unconditional theorem |

Full enumeration: [`REGISTRY.md`](../REGISTRY.md) · machine JSON: [`registry/theorems.json`](../registry/theorems.json).

### Theme distribution (module-name clustering; not a second ledger)

| Theme cluster | Entries |
|---------------|--------:|
{theme_rows}

---

## 3. Flagship results (registry-backed samples)

Only names that exist in the current registry are listed. Partners should click
through to the declaration, not treat the blurb as a substitute proof.

{chr(10).join(flagship_lines) if flagship_lines else "*No flagship patterns matched the current registry.*"}

### Certificate factory (unit of progress)

Recent program direction: certificates as first-class artifacts under
`registry/certificates/`. Present units: {cert_txt}.

---

## 4. Explicit NON-CLAIMS

Marketing and partner decks **must not** promote the following as unconditional
closes. Status is taken from the registry when the name is present.

| Topic | Registry name | Register | Note |
|-------|---------------|----------|------|
{chr(10).join(non_claim_lines)}

### All CONDITIONAL entries ({conditional})

| Name | Module |
|------|--------|
{chr(10).join(cond_lines) if cond_lines else "| *(none)* | |"}

### All DISCHARGED entries ({discharged})

| Name | Module |
|------|--------|
{chr(10).join(disc_lines) if disc_lines else "| *(none)* | |"}

### All CONJECTURE entries ({conjecture})

| Name | Module |
|------|--------|
{chr(10).join(conj_lines) if conj_lines else "| *(none)* | |"}

---

## 5. Multi-prover operations

Heterogeneous engines write candidates; **one registry** decides the badge.

| Role | Engine | What it is trusted for |
|------|--------|-------------------------|
| **Independent verify** | **AXLE** (Axiom Lean Engine) | Statement + proof re-check at pinned `lean-4.32.0`; required for PROVED |
| **Hard classical generation** | **Aristotle** (Harmonic) | Proof generation / port for difficult targets; **never** a substitute for AXLE |
| **Frontier reduce / modules** | Codex / Grok (parallel tools) | Schema reduction, scaffolding, large module drafts; gated before tip merge |
| **Orchestration + hygiene** | Local scripts + human tip | `gen_registry`, no-theater lint, dependency firewall, settle/certificates |

**Triple verification ideal for PROVED:**

1. Local `lake build` on pinned toolchain
2. Local `#print axioms` ⊆ standard three
3. AXLE `verified` at named environment

**Today’s registry field reality:** AXLE + axiom gate are populated for all
listed entries; the `lake_build` stamp is still largely `pending` (see below).
That is an operational caveat, not a license to inflate PROVED.

---

## 6. Caveats partners must know

### 6.1 AXLE vs local lake

| Leg | Status in this export |
|-----|------------------------|
| AXLE independent check | **{axle_verified}/{vstats['n']}** verdict `verified` @ `{env_main}` |
| Axioms clean flag | **{vstats['axioms_ok']}/{vstats['n']}** `axioms_ok: true` |
| Local `lake_build` stamp | **{lake_pending}/{vstats['n']}** marked `pending` |

**Implication:** Partner-grade “verification company” narrative requires a
reproducible local/CI `lake build` leg alongside AXLE. Treat current PROVED as
**AXLE-attested + axiom-gated**, with local lake stamp not yet written into
every registry row. Third parties should still run:

```bash
lake exe cache get
lake build
```

on the tip commit above.

### 6.2 Counting discipline

- **Registry PROVED** ({proved}) is the only number safe for partner headlines.
- Campaign / historical “theorems attempted” totals are **not** interchangeable with PROVED.
- DEFINITION ({definition}) supports the API surface; do not add it to PROVED.
- DISCHARGED ({discharged}) is a success story (conditionals closed) — **not** extra PROVED.

### 6.3 No theater

Excluded failure modes (definitional theater, ℝ-mod collapse, smuggled
`native_decide`, overtitling, etc.) are documented in process notes; they are
not silently upgraded. See honesty commitments in the repo root `README.md` and
[`docs/NEW-ERA.md`](NEW-ERA.md).

---

## 7. Strategic reading (for partners)

The pentagonal / Brockian math program is the **crucible**. The **product** is
verification-gated reasoning: formalize → multi-prover verify → deploy only what
the ledger proves.

| Deploy vector | Role of this program |
|---------------|----------------------|
| **QuantumProof / IonQ** | Formal security/entropy/PQC properties with registry badges |
| **SAIR / distillation** | Train and score on machine-checked traces, not unverified CoT |
| **Public registry surface** | Observatory / torus must pull badges from this SSOT |

Full partner strategy brief (tone, 90-day plan, risk table):

→ **[`docs/partner/2026-08-02-verified-intelligence-strategy-brief.md`](partner/2026-08-02-verified-intelligence-strategy-brief.md)**

---

## 8. How to re-verify this report

```bash
# 1. Pin the tip
git rev-parse HEAD

# 2. Recompute counts (must match §2)
python3 -c "import json; d=json.load(open('registry/theorems.json')); print(d['summary'])"

# 3. Regenerate this document
python3 scripts/gen_program_report.py

# 4. Optional: full registry + paper tables from attestations
python3 scripts/gen_registry.py
python3 scripts/gen_paper_theorem_table.py
```

**Pin phrase for external one-pagers:**

> As of commit `{tip['short']}` ({report_date}): **{proved} PROVED**, **{definition} DEFINITION**, **{conditional} CONDITIONAL**, **{discharged} DISCHARGED**, **{conjecture} CONJECTURE** — from `registry/theorems.json`.

---

*This file is generated. Edit `scripts/gen_program_report.py` for structure; never hand-edit counts.*
"""
    return body


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY)
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    ap.add_argument("--repo", type=Path, default=ROOT)
    args = ap.parse_args()

    reg_path = args.registry if args.registry.is_absolute() else args.repo / args.registry
    out_path = args.out if args.out.is_absolute() else args.repo / args.out

    registry = load_registry(reg_path)
    tip = git_tip(args.repo)
    n_att = attestation_count(args.repo)
    certs = certificate_names(args.repo)
    text = render_report(registry, tip, reg_path.relative_to(args.repo) if reg_path.is_relative_to(args.repo) else reg_path, n_att, certs)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text, encoding="utf-8")
    summary = registry.get("summary") or count_registers(registry.get("theorems") or [])
    print(f"wrote {out_path}")
    print(f"summary: {summary}")
    print(f"tip: {tip['short']} {tip['subject']}")


if __name__ == "__main__":
    main()
