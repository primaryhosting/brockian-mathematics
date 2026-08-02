#!/usr/bin/env python3
"""Seed starter problem cards across all domains."""
from __future__ import annotations

import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from pipeline.adapters.erdos import make_erdos_card  # noqa: E402
from pipeline.core.schema import ProblemCard, save_card  # noqa: E402


def seeds() -> list[ProblemCard]:
    cards: list[ProblemCard] = []

    # --- Erdős (mix of open-priority + known-solved literature) ---
    cards.append(
        make_erdos_card(
            90,
            "Unit distance problem (planar)",
            "What is the maximum number of unit distances among n points in the plane?",
            external_status="solved",
            tags=["erdos", "geometry", "combinatorics"],
            difficulty=5,
            priority=20,
            notes="External solved (2026 reports). LITERATURE unless we re-formalize.",
        )
    )
    cards.append(
        make_erdos_card(
            1,
            "Erdős problem 1 (seed placeholder — verify statement on site)",
            "See https://www.erdosproblems.com/1 for the canonical statement. "
            "This card is a pipeline seed; refresh statement before attack.",
            external_status="open",
            tags=["erdos", "number-theory"],
            difficulty=5,
            priority=40,
            notes="Replace statement after live sync.",
        )
    )
    cards.append(
        make_erdos_card(
            28,
            "Distinct distances (related seed)",
            "Erdős distinct distances-type questions: lower bounds on distinct distances "
            "determined by n points in the plane. Canonical statement on erdosproblems.com.",
            external_status="open",
            tags=["erdos", "geometry", "combinatorics", "finite"],
            difficulty=4,
            priority=70,
            notes="High yield if reduced to finite geometric configurations + compute.",
        )
    )
    cards.append(
        make_erdos_card(
            52,
            "Erdős–Turán conjectures family (seed)",
            "Additive combinatorics / discrepancy style Erdős problems. "
            "Confirm exact numbering and statement on erdosproblems.com before formal work.",
            external_status="open",
            tags=["erdos", "additive-combinatorics"],
            difficulty=5,
            priority=55,
        )
    )

    # --- Distillation / SAIR equational ---
    cards.append(
        ProblemCard(
            id="distill-etp-stage1",
            domain="distillation",
            title="SAIR Mathematics Distillation Challenge — Equational Theories Stage 1",
            statement=(
                "Design a cheat sheet (≤10 KB) that improves weak LLM accuracy on true/false "
                "universal-algebra implications from the Equational Theories Project "
                "(~22M implications). Stage 1 is T/F only; do not overclaim Stage 2 proof ability."
            ),
            status="open",
            source={
                "url": "https://competition.sair.foundation/competitions/mathematics-distillation-challenge-equational-theories-stage1/overview",
                "citation": "Tao–Davis, SAIR Mathematics Distillation Challenge (2026)",
                "external_status": "open",
            },
            difficulty=3,
            tags=["distillation", "equational", "sair", "llm"],
            formal_targets=[{"kind": "cheatsheet", "name": "etp_stage1", "path": "pipeline/distill/cheatsheets/etp_v0.txt"}],
            attack_modes=["distill", "compute", "refute"],
            verification={
                "backend": "distillation_harness",
                "criteria": [
                    "size ≤ 10240 bytes",
                    "accuracy lift vs baseline on held-out set",
                    "human review before competition submit",
                ],
            },
            risk_tier=1,
            notes="Primary distillation track. Build cheatsheets under pipeline/distill/cheatsheets/.",
            priority=90,
        )
    )
    cards.append(
        ProblemCard(
            id="distill-etp-stage2",
            domain="distillation",
            title="SAIR Distillation Stage 2 — proof or counterexample",
            statement=(
                "Beyond T/F: supply probability plus a deterministically verifiable certificate "
                "(Lean proof or explicit counterexample magma) for equational implications."
            ),
            status="open",
            source={
                "url": "https://competition.sair.foundation/",
                "citation": "SAIR Stage 2 (design evolving)",
                "external_status": "open",
            },
            difficulty=4,
            tags=["distillation", "equational", "lean", "sair"],
            formal_targets=[
                {"kind": "lean_theorem", "name": None, "path": None},
                {"kind": "counterexample", "name": None, "path": None},
            ],
            attack_modes=["formalize", "refute", "dual_prover", "distill"],
            verification={
                "backend": "hybrid",
                "criteria": ["Lean kernel check or explicit finite counterexample", "optional AXLE"],
            },
            risk_tier=1,
            priority=75,
        )
    )

    # --- SAIR foundation tracker ---
    cards.append(
        ProblemCard(
            id="sair-program-tracker",
            domain="sair",
            title="SAIR.foundation program & challenge tracker",
            statement=(
                "Track SAIR (Foundation for Science and AI Research) challenges and cooperative "
                "programs. AI-for-science and science-for-AI: every claim needs a verification backend."
            ),
            status="open",
            source={
                "url": "https://sair.foundation/",
                "citation": "SAIR — Tao et al.",
                "external_status": "open",
            },
            difficulty=2,
            tags=["sair", "meta"],
            formal_targets=[{"kind": "paper", "name": "tracker", "path": None}],
            attack_modes=["literature", "decompose"],
            verification={"backend": "literature", "criteria": ["citation freshness", "no auto-submit"]},
            risk_tier=1,
            notes="Meta card: spawn child cards when new challenges launch.",
            priority=60,
        )
    )

    # --- Math (Brockian open cores as pipeline cards) ---
    cards.append(
        ProblemCard(
            id="math-gate1-lp-continuous-bounded",
            domain="math",
            title="Gate 1: continuous bounded potential → limit-point",
            statement=(
                "Extend Weyl limit-point results beyond continuous-constant and special cases "
                "toward continuous bounded V. Do not claim full Gate 1 ESA until deficiencies close."
            ),
            status="partial",
            source={"citation": "Brockian WeylLimitPointContinuous + scaffolds", "external_status": "partial"},
            difficulty=5,
            tags=["spectral", "analysis", "weyl", "gate1"],
            formal_targets=[
                {"kind": "lean_theorem", "name": "Brockian.Weyl.LimitPointContinuous.*", "path": "Brockian/WeylLimitPointContinuous.lean"}
            ],
            attack_modes=["formalize", "decompose", "dual_prover"],
            verification={"backend": "lean_axle", "criteria": ["AXLE verified", "axioms clean", "no theater"]},
            risk_tier=1,
            notes="Linked to Brockian formal program.",
            priority=85,
            ledger_refs=["Brockian.Weyl.LimitPointContinuous"],
        )
    )
    cards.append(
        ProblemCard(
            id="math-rh-schema",
            domain="math",
            title="RH schema (honest conditional — never claim PROVED)",
            statement=(
                "Riemann Hypothesis remains open. Pipeline tracks the Brockian spectral/ξ schema "
                "and reductions only. Any 'proof' without independent formal verification is BLOCKED."
            ),
            status="conditional",
            source={"citation": "Brockian RiemannScaffold / SpectralGate1", "external_status": "open"},
            difficulty=5,
            tags=["rh", "number-theory", "spectral"],
            formal_targets=[{"kind": "lean_def", "name": "Brockian.Riemann.*", "path": "Brockian/RiemannScaffold.lean"}],
            attack_modes=["decompose", "formalize"],
            verification={"backend": "lean_axle", "criteria": ["schema only", "overclaim firewall"]},
            risk_tier=3,
            notes="risk_tier=3 millennium-class. Register stays CONDITIONAL/SCAFFOLD.",
            priority=30,
        )
    )
    cards.append(
        ProblemCard(
            id="math-goldbach-local-wheels",
            domain="math",
            title="Goldbach local wheels & singular series (finite layer)",
            statement=(
                "Continue finite Goldbach covariance / local wheel / singular series formalization. "
                "Full Goldbach remains open; do not promote local results to global PROVED."
            ),
            status="partial",
            source={"citation": "Brockian Goldbach* SingularSeries*", "external_status": "partial"},
            difficulty=3,
            tags=["goldbach", "sieve", "finite", "number-theory"],
            formal_targets=[{"kind": "lean_theorem", "name": "Brockian.Goldbach*", "path": "Brockian/"}],
            attack_modes=["formalize", "compute"],
            verification={"backend": "lean_axle", "criteria": ["AXLE", "honest local claims"]},
            risk_tier=1,
            priority=80,
        )
    )

    # --- Physics ---
    cards.append(
        ProblemCard(
            id="physics-schrodinger-esa-bridge",
            domain="physics",
            title="Schrödinger operator essential self-adjointness (model)",
            statement=(
                "Mathematical model: essential self-adjointness of −Δ+V under named deficiency / "
                "Kato-class hypotheses. Experimental physics claims are out of scope; prove math about the model."
            ),
            status="conditional",
            source={"citation": "Brockian WeylSchrodingerESA", "external_status": "partial"},
            difficulty=4,
            tags=["spectral", "schrodinger", "operator-theory"],
            formal_targets=[{"kind": "lean_theorem", "name": "Brockian.Weyl.SchrodingerESA.*", "path": "Brockian/WeylSchrodingerESA.lean"}],
            attack_modes=["formalize", "decompose"],
            verification={"backend": "lean_axle", "criteria": ["named hypotheses explicit", "AXLE"]},
            risk_tier=2,
            priority=70,
        )
    )

    # --- CS ---
    cards.append(
        ProblemCard(
            id="cs-sieve-count-parity",
            domain="cs",
            title="Executable sieve counts match Lean admissibility cards",
            statement=(
                "Implement a small Python/C reference that computes admissible residue counts "
                "for k-tuples and matches Lean theorems (CRT product, diagonal cases)."
            ),
            status="open",
            source={"citation": "Brockian Admissibility*", "external_status": "open"},
            difficulty=2,
            tags=["sieve", "implementation", "testing"],
            formal_targets=[
                {"kind": "implementation", "name": "sieve_counts", "path": "pipeline/artifacts/cs/"},
                {"kind": "compute_cert", "name": "golden_counts", "path": None},
            ],
            attack_modes=["compute", "formalize"],
            verification={"backend": "compute", "criteria": ["golden hash match", "optional Lean link"]},
            risk_tier=1,
            priority=65,
        )
    )

    # --- Quantum ---
    cards.append(
        ProblemCard(
            id="quantum-free-laplacian-plancherel",
            domain="quantum",
            title="Free Laplacian Plancherel / Fourier multiplier scaffold",
            statement=(
                "Formal and analytic control of free −Δ on L²(ℝⁿ) via Fourier multipliers / Plancherel. "
                "Supports quantum kinetic energy term in Gate-1 style models."
            ),
            status="scaffolded",
            source={"citation": "Brockian FreeLaplacianPlancherel / WeylFreeLaplacian", "external_status": "partial"},
            difficulty=4,
            tags=["quantum", "spectral", "fourier"],
            formal_targets=[{"kind": "lean_theorem", "name": "Brockian.FreeLaplacian*", "path": "Brockian/FreeLaplacianPlancherel.lean"}],
            attack_modes=["formalize", "decompose", "dual_prover"],
            verification={"backend": "lean_axle", "criteria": ["AXLE", "no overclaim of interacting case"]},
            risk_tier=1,
            priority=72,
        )
    )

    return cards


def main() -> int:
    written = []
    for card in seeds():
        path = save_card(card)
        written.append(str(path))
    print(f"seeded {len(written)} cards:")
    for w in written:
        print(f"  {w}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
