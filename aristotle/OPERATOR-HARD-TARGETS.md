# Operator Hard Targets

Prepared for Harmonic / Aristotle on 2026-08-03. These are exact frontier
statements and are intentionally not imported by `Brockian.lean`.

1. `oscillator-esa/target.lean`: ESA of the concrete Schwartz harmonic oscillator.
2. `oscillator-compact-resolvent/target.lean`: compactness of both canonical unit
   resolvents, assuming only the exact oscillator ESA input.
3. `free-laplacian-schwartz-intertwining/target.lean`: the concrete Schwartz
   `-D2` operator is a restriction of the Fourier-defined free Laplacian.
4. `kato-bounded-unbounded-transfer/target.lean`: the full bounded
   self-adjoint perturbation theorem for an unbounded ESA core.
5. `free-laplacian-schwartz-corrected/target.lean`: the corrected physical
   Fourier multiplier `4*pi^2*xi^2`, its maximal-multiplier ESA, and the
   Schwartz-core restriction theorem.

Integration contract: returned proofs must retain the exact statements, pass
AXLE at Lean 4.32, have no `sorryAx`, and pass `no_theater_lint.py`. A solution
to target 1 does not imply target 2. Target 3 is needed before transferring the
spectral free-Laplacian theorem to the pre-existing differential core.

## Harmonic projects

| Target | Project |
|---|---|
| Oscillator ESA | `ed7ece6e-d1a2-4004-9a2a-511fe9ba5818` |
| Oscillator compact resolvent | `6fc04ed4-e69c-4f03-a655-1189d448a180` |
| Free-Laplacian Schwartz intertwining | `0998b403-c5ff-48e6-bb38-962f9d015329` |
| Full bounded Kato transfer | `7bfd75f8-4755-4eed-85ee-20b2391e8a94` |

The original free-Laplacian intertwining project `0998b403-...` is retained as
an audit artifact but its target is false under Mathlib's Fourier normalization:
`M_{xi^2}` conjugates to `-(4*pi^2)^{-1} d^2/dx^2`. It must never be integrated.
The corrected project ID is recorded here after submission.

Corrected free-Laplacian project: `87ef7b72-ec83-4b0e-8455-f85daa6e3029`.

## Status at integration

| Target | Status |
|---|---|
| Oscillator ESA | `COMPLETE_WITH_ERRORS`; original proof hole unchanged |
| Oscillator compact resolvent | Running |
| Original unscaled intertwining | Refuted by the proved `(2*pi)^2` normalization identity |
| Full bounded Kato transfer | Complete; AXLE-audited and integrated as `Brockian.Weyl.KatoRellich` |
| Corrected free-Laplacian | Running; its spectral ESA portion is independently integrated as `Brockian.WeylFreeLaplacianCorrected` |

All submissions were accepted by the Harmonic API on 2026-08-03. The
service warns that it prefers Lean 4.28; every return must therefore be ported
and independently checked at the repository's Lean 4.32 toolchain.
