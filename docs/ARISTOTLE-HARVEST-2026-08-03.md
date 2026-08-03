# Aristotle Harvest Audit - 2026-08-03

This ledger records the disposition of the 19 Aristotle return archives supplied on
2026-08-03. A return is not accepted because Aristotle labels it solved: canonical modules
must preserve the target statement, pass AXLE at Lean 4.32, have an acceptable axiom set,
and pass the no-theater lint.

| Archive prefix | Mathematical content | Disposition |
|---|---|---|
| `1bab1c65` | RH/operator sketch | Rejected: `xi := 0`, zero spectral data, `True` slots, and conditional RH packaging |
| `2c8bde2d` | Two squares | Duplicate of an integrated theorem |
| `4c48bb51` | Erdos-Ginzburg-Ziv | Already integrated by a peer in `3ef6a49` |
| `9f4eecfe` | Phase-depth torus | Clean substantive subset integrated; vacuous `True`/`False` scaffolds excluded |
| `11b14535` | Frobenius McNugget | Already integrated by a peer in `4973dc9` |
| `18ee0406` | Sieve Hamiltonian | Clean CRT/triple-admissibility subset integrated; later `sorry` declarations excluded |
| `20c31983` | Mersenne exponent | Duplicate of an integrated theorem |
| `40f28fb5` | Even perfect modulo 9 | Ported statement-preservingly from 4.28 and integrated |
| `42d202c5` | Goldbach comb | Duplicate of an integrated theorem |
| `56bc9245` | Even perfect is triangular | Duplicate of an integrated theorem |
| `73e0a459` | Odd perfect modulo 4 | Duplicate of an integrated theorem |
| `95d97500` | Elementary plates | Ported to 4.32; `native_decide` replaced by kernel-safe `decide`; integrated |
| `46318bec` | Euler form for odd perfect numbers | Duplicate of an integrated theorem |
| `1772947a` | Korselt implies Carmichael | Duplicate of an integrated theorem |
| `a301024c` | Wilson theorem | Duplicate of an integrated theorem |
| `ab22201e` | Frobenius above the bound | Already integrated by a peer in `28ffa12` |
| `b245c702` | Affine selection | Clean finite selection/Jacobi subset integrated; two `sorry` theorems and a `True` asymptotic excluded |
| `cd725c65` | Two squares | Duplicate of an integrated theorem |
| `cf31a33b` | Lucas theorem | Already integrated by a peer in `07cb8eb` |

## Integrated modules

- `Brockian.EvenPerfectMod9`
- `Brockian.ElementaryPlates`
- `Brockian.PhaseDepthTorus`
- `Brockian.TripleAdmissibility`
- `Brockian.AffineSelection`

The five-module harvest added 44 `PROVED` declarations and 14 definitions, with no new
conditionals or conjecture markers. The canonical integration is commit `ac48a46`.

## Operator work shipped in the same cycle

`Brockian.WeylMaximalMultiplication` proves essential self-adjointness for the maximal
quadratic multiplication operator and transfers it through a unitary equivalence. This gives
a concrete Fourier-defined free Laplacian with essential self-adjointness. It does not yet
identify that operator with the existing Schwartz-core differential operator `-f''`; that
intertwining theorem remains a named hard target.

Four exact targets were submitted to Harmonic/Aristotle and are recorded in
`aristotle/OPERATOR-HARD-TARGETS.md`: oscillator ESA, oscillator compact resolvent,
Schwartz/Fourier free-Laplacian intertwining, and the bounded unbounded-operator Kato transfer.

## Verification record

All five canonical harvest modules and `Brockian.WeylMaximalMultiplication` passed AXLE with
the Lean 4.32 environment, axiom probing, and `scripts/no_theater_lint.py`. The registry and
manifest consistency checks passed. A full local `lake build` was intentionally not used for
this harvest because local compute is constrained; AXLE supplied the independent Lean kernel
checks.
