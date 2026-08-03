# Riemann Labs Corpus Audit Reconciliation

Date: 2026-08-03

## BLUF

The external Lean Corpus Executive Roadmap is useful prioritization, but it is
not the current verification authority. It inspected 64 source versions under
`/mnt/data`, did not run Lean or Lake, and mixed historical Aristotle returns
with the canonical repository. The current source of truth is the root-imported
registry at commit `77fde5e`:

- 11,216 registered declarations
- 10,568 `PROVED`
- 581 `DEFINITION`
- 20 `CONDITIONAL`
- 7 `DISCHARGED`
- 40 `CONJECTURE`

The public Torus export is sanitized, secret-scanned, and validated against all
lab manifests. AXLE and the registry firewall, not a static file audit, decide
whether a declaration is publishable as verified.

## Twelve-target reconciliation

| External recommendation | Canonical disposition | Current evidence / next move |
|---|---|---|
| Replace the universal tuple-cardinality axiom | **Closed in the canonical design** | `Brockian.AdmissibilityKTuple` proves the forbidden-image cardinality law and pair/triple specializations; `Brockian.AdmissibilityCRTGeneral` proves product-CRT formulas. Do not reintroduce `UniversalTheorem.lean`. |
| Finish central SieveHamiltonian counts | **Partially open** | `Brockian.Sieve` contains only AXLE-clean keepers. `Brockian.TripleAdmissibility` proves CRT compatibility and multiplicativity. The faithful prime-local triple count and resulting wheel/component formulas remain attackable. |
| Complete PhaseDepth campaign names | **Do not restore the old names blindly** | `orbit_single_cycle`, `twin_wheel_two`, and `three_road_balance_105` were deliberately dropped because the supplied statements used vacuous `True`/`False` scaffolding. `Brockian.PhaseDepthTorus` already proves period 25, minimality, injectivity on one period, and the local twin grammar. Author faithful replacement statements first. |
| Finish AffineSelection structure/correlation | **Dihedral side closed; correlation open** | The dihedral action/isomorphism and Goldbach translation/reflection readings are proved in `Brockian.AffineSymmetry`, `Brockian.Automorphism.Full`, and `Brockian.GoldbachSelectionRule`. A general quadratic affine-correlation theorem remains a good target. |
| Prove the Goldbach wheel kernel | **Finite wheels closed; general kernel open** | Exact local covariance and finite `K23`, `K235`, and `K2357` products are proved. The original `wheel_kernel` statement was rejected as false/ill-formed. Define the normalized wheel weight and shifted autocorrelation before proving a general CRT product. |
| Instantiate the mod-11 phase system | **Open** | No canonical root module currently constructs the exact order-five Dirichlet character modulo 11. This remains a clean finite/arithmetic target after checking Mathlib's character API. |
| Complete full Korselt criterion | **Partially open** | The forward arithmetic criterion, concrete examples, Korselt API, and oddness are proved across `Brockian.KorseltCarmichael` and `Brockian.CarmichaelKorselt`. A two-way equivalence with a fully defined Carmichael-number predicate remains open. |
| Consolidate perfect-number modules | **Mathematics largely closed; packaging open** | Odd Euler form, odd-mod-4, reciprocal-sum, even-mod-9, triangularity, Mersenne, multiperfect, hyperperfect, quasiperfect, superperfect, unitary-perfect, and perfect-totient results are root-imported. Attribution, shared Euclid-Euler infrastructure, and duplicate-proof reduction remain useful engineering work. |
| Modularize Sylvester-Schur | **Quarantined, not release-ready** | The supplied monolith passed its older environment but failed the required Lean 4.32 AXLE port in derivative/reassociation obligations. It must not be advertised as part of the current verified core until the 4.32 proof is repaired and re-attested. |
| Refactor Wolstenholme | **Flagship theorem closed; refactor open** | `Brockian.Wolstenholme.wolstenholme` is root-imported and AXLE-verified at 4.32. Extracting reusable congruence lemmas and adding the classical equivalent form is a sound next package. |
| Eliminate `native_decide` from release modules | **Scope correction required** | The cited canonical files use kernel-checked `by decide`, not `native_decide`; `EvenPerfectLastDigit` is not root-imported. Explanatory symbolic proofs may improve readability, but this is not presently an AXLE trust defect. |
| Replace placeholder asymptotics | **Immediate integrity target** | `GoldbachCovarianceTransfer` is honestly registered as a conjecture, but its body still ends in `True` and is not a faithful mathematical statement. Define concrete counting/residual/kernel functions and a quantified limit or error bound before exposing it in a public lab. |

## Corrected priority order

1. Replace `GoldbachCovarianceTransfer` with a faithful, falsifiable statement.
2. State and prove the prime-local triple count, then derive the CRT wheel count.
3. Define the normalized Goldbach wheel autocorrelation and prove its finite CRT factorization.
4. Construct the concrete order-five character modulo 11.
5. Prove the quadratic affine-correlation theorem using the existing Jacobi-sum lemmas.
6. Complete the Carmichael predicate and both directions of Korselt's criterion.
7. Repair and modularize Sylvester-Schur at Lean 4.32 before release.
8. Extract reusable Wolstenholme lemmas and the classical equivalent form.
9. Consolidate perfect-number imports and attribution without changing theorem content.
10. Continue the operator lane: oscillator ESA and the concrete weighted compact embedding.

## Public communication rule

The external grades may be shown as an **advisory static audit**, never as a
verified certificate. Riemann Labs should obtain theorem status and counts only
from `/verified-registry.json`; `CONDITIONAL` and `CONJECTURE` nodes must remain
non-green. The concrete bounded-continuous-potential Gate-1 theorem is verified.
The RH spectral correspondence, oscillator ESA, and compact resolvent remain
open.
