# Gate-1 one-brick status (2026-08-02 — Grok)

> **Superseded / resolved:** the red weak-regularity, energy, and concrete closure files listed below were repaired, independently AXLE-verified, root-imported, and shipped in `a5ff22d`. The current concrete result is ESA plus a self-adjoint closure and unit resolvents for the one-dimensional Schwartz-core operator with continuous bounded real potential. This historical note remains as an audit trail.

## Shipped brick (green)

**KatoBounded** @ `b90530b` — bounded Kato–Rellich range-density.

| Decl | Register | AXLE |
|------|----------|------|
| `Brockian.Weyl.KatoTarget.isSelfAdjoint_add` | PROVED | verified @4.32 |
| `Brockian.Weyl.KatoTarget.dense_range_add_sub_of_selfAdjoint` | PROVED | verified @4.32 |

**Honesty:** BOUNDED case only. Does **not** discharge Gate-1 for the unbounded Brockian Schrödinger operator. Upstream closed-range package (`ClosedRangeClosure`, `ClosedShiftedRanges`) remains the ESA→resolvent assembly base.

Aristotle mirror: `aristotle/kato-bounded/KatoBounded.lean` synced to shipped body (no `sorry`).

## Blocked bricks (do not integrate)

| File | Why blocked |
|------|-------------|
| `Brockian/WeylWeakRegularityClosed.lean` | Attest `module_verified: false`; 8× `sorryAx` |
| `Brockian/WeylWeakEnergy.lean` | Imports red WeakRegularityClosed |
| `Brockian/WeylSchrodingerGate1Closed.lean` | Depends on WeakEnergy |

## Still CONDITIONAL (honest open rungs)

- `DeficiencyODE.*_of_weakRegularity` (2)
- `KatoUnbounded.essentiallySelfAdjoint_perturb`
- `FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel`
- `SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode`

Next real brick for Claude/Codex: **weak regularity A1** until AXLE-green, then energy + Gate1Closed assembly.
