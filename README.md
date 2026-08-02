# Brockian Mathematics — Verified Core

A Lean 4 formalization of the "Curved Number Line" / Brockian program: the pentagonal,
golden-ratio structure of prime residues and constellations, its dihedral symmetry, and
the honest scaffolding of a Hilbert–Pólya-style attack on the Riemann Hypothesis.

**What makes this different from most AI-assisted math: every "PROVED" result is
independently machine-verified, and the repository refuses to claim anything the build
does not earn.**

## Multi-domain problem attack pipeline

The same process (intake → triage → decompose → attack → verify → **derived register** → publish)
is generalized beyond Brockian Lean for:

- **Erdős problems** ([erdosproblems.com](https://www.erdosproblems.com/))
- **SAIR distillation challenges** (equational theories cheat sheets ≤10KB)
- **SAIR.foundation** program tracking
- **Mathematics, physics, CS, quantum** open problems

See [`pipeline/README.md`](pipeline/README.md) and the design spec
[`docs/superpowers/specs/2026-08-02-problem-attack-pipeline.md`](docs/superpowers/specs/2026-08-02-problem-attack-pipeline.md).

```bash
python3 -m pipeline.scripts.seed_catalog
python3 -m pipeline.scripts.pipeline_cli queue
python3 -m pipeline.scripts.pipeline_cli ledger
```

## The verification discipline

Each declaration carries exactly one *register*, derived mechanically — never hand-asserted:

| Register | Meaning | Gate |
|----------|---------|------|
| **PROVED** | sorry-free, `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, no `native_decide`, **and** independently verified by AXLE | all three legs must pass |
| **COMPUTATION** | finite `decide` / `native_decide` checks | recorded as computation, never PROVED |
| **CONDITIONAL** | depends on a named hypothesis; records its rung (classical / literature / open) | never counted as unconditional evidence |
| **CONJECTURE** | a named `def` / Prop container | never typed as a theorem |

The register lives in a machine-generated registry (`registry/theorems.json`, rendered in
[`REGISTRY.md`](REGISTRY.md)) that the forthcoming paper and website both consume as the
single source of truth. A theorem cannot be labelled PROVED unless the build and an
independent third-party check both agree.

### Triple verification

A **PROVED** theorem passes three independent legs:

1. **local `lake build`** on the pinned toolchain,
2. **local `#print axioms`** — only the three standard axioms,
3. **AXLE** ([axle.axiommath.ai](https://axle.axiommath.ai)) — an *independent* cloud
   Lean 4 + Mathlib prover that re-checks the proof at a named environment (`lean-4.32.0`),
   including statement fidelity.

This directly closes the intake ledger's long-standing caveat that no independent build had
ever been run. Per-declaration attestations live in `registry/attestations/`.

## Verified so far

See [`REGISTRY.md`](REGISTRY.md) for the live list. Current PROVED headline results:

- **The q−ν admissibility law** (`Brockian.Admissibility`): over `ZMod q`, exactly `q − 2`
  start residues are admissible for a nonzero gap; corollaries give **1** residue mod 3
  (the twin-prime constraint) and **3** mod 5 (the Brockian case).
- **The Goldbach local-covariance kernel** (`Brockian.GoldbachComb`): the exact local count
  `g_p(c) = p − 2 + [c=0]`, its centered spike, and the two-case covariance theorem, for
  every prime `p`. The transfer to the global Goldbach residual is a **named conjecture**,
  not a claim.

## Honesty commitments (non-negotiable, from the intake ledger)

- **Nothing is faked to get a green build**: no `sorry`/`admit`, no `maxHeartbeats`
  inflation to hide a hang, no axiom added to force a close, no `native_decide` smuggled
  into a PROVED theorem.
- **Open problems stay open**: the unbounded Hamiltonian (Gate 1), the Riemann Hypothesis,
  and the Goldbach transfer are honestly marked open — their scaffolding is formalized, their
  open cores are not pretended shut.
- **Excluded work is documented**: declarations rejected during the audit (definitional
  theater, ℝ-mod collapse, Nat-division exponent traps, ex-falso conditionals, overtitling,
  …) are listed with their failure mode, not silently dropped.
- **Provers are never trusted on their own word**: the independent gates run on every
  generated proof, because a self-reported success can smuggle a disguised `sorry`.

## Environment

- **Lean** `leanprover/lean4:v4.32.0`, **Mathlib** `v4.32.0`.
- **Proof generation / porting**: [Aristotle](https://aristotle.harmonic.fun) (Harmonic) and
  hand-porting, raced per target.
- **Independent verification**: [AXLE](https://axle.axiommath.ai) (Axiom Lean Engine).

## Building

```bash
lake exe cache get   # prebuilt Mathlib oleans
lake build
```

## New Era Mathematics

Charter: [`docs/NEW-ERA.md`](docs/NEW-ERA.md) · Gallery: [`observatory/era.html`](observatory/era.html)

## Observatory (public claim surface)

Book claim IDs (Curved Number Line margins, e.g. `GC-1`, `BM-MAP-001`) map to Lean
declarations via a hand-authored table; **badges are derived** from the registry
and never hand-painted.

```bash
python3 scripts/gen_registry.py      # registry/theorems.json from AXLE attestations
python3 scripts/gen_claims.py        # observatory/claims.yaml + claims.json
python3 scripts/gen_observatory.py   # observatory/index.html
open observatory/index.html          # or any static file server
open observatory/era.html            # New Era gallery (charter surface)
```

| Path | Role |
|------|------|
| `observatory/claim_map.yaml` | claim ID → Lean names (edited by hand) |
| `observatory/claims.yaml` | generated claims + full declaration dump |
| `observatory/index.html` | static page: badge, book ref, declarations, AXLE |

## Layout

```
Brockian/            the verified theme modules (one mathematical theme each)
registry/            theorems.json (generated) + per-module AXLE attestations
observatory/         public claim surface (map + generated claims + HTML)
provenance/          verdicts.yaml — hand-authored verdicts + provenance (audited)
scripts/             axle_client.py, gen_registry.py, gen_claims.py, gen_observatory.py, …
Archive/             retired inputs (old catalog), kept for reference, not built
docs/superpowers/    the design spec and implementation plan
```

## License

MIT License. Copyright 2026 Christopher Brock.

## Acknowledgments

Independent verification by [AXLE](https://axle.axiommath.ai) (Axiom) and
[Aristotle](https://aristotle.harmonic.fun) (Harmonic). Built on
[Mathlib](https://github.com/leanprover-community/mathlib4).
