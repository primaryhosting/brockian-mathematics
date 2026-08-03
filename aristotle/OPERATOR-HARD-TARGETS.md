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

All four submissions were accepted by the Harmonic API on 2026-08-03. The
service warns that it prefers Lean 4.28; every return must therefore be ported
and independently checked at the repository's Lean 4.32 toolchain.
