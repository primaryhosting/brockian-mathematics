# Weyl modules: build repair and the E12 boundary

Baseline: `ed95b048e7e5ecb6513326766b9efafeaba506aa`.
Diagnostic CI run: [35158672068](https://github.com/primaryhosting/brockian-mathematics/actions/runs/35158672068).
The diagnostic compiled a closure of 27 modules under Lean 4.32.0; 23 compiled
and four failed. Those counts describe that bounded set, not the full corpus.

After the four name-resolution repairs, **all 27 compiled** in
[run 35159492433](https://github.com/primaryhosting/brockian-mathematics/actions/runs/35159492433),
using the pinned compiler and `-DautoImplicit=false`. This is a compilation
receipt, not a completed whole-corpus build or refreshed external attestation.

| Failed source | Reproduced defect | Review-branch correction |
|---|---|---|
| ConfiningSpectralShape | Unresolved primeGaussian / primeGaussianMulCLM family | Open the defining SpectralGate1 namespace |
| WeylWeakRegularityClosed | `conj` unavailable and ensuing definitional equality failure | Open the ComplexConjugate notation scope |
| WeylWeakRegularityDischarge | Unqualified uIoc_subset_uIcc | Use Set.uIoc_subset_uIcc |
| WeylKatoRellichTransfer | EssentiallySelfAdjoint unresolved | Open the defining Weyl.Operator namespace |

These edits preserve the intended statements. They require a new compilation
receipt and refresh of source-bound attestations before promotion. The checker
now passes `-DautoImplicit=false`, matching the repository's lakefile option,
so unresolved identifiers cannot become hidden implicit parameters.

## What E12 actually rules out

Use N_ζ(T) for **all** nontrivial ζ zeros with 0<Im(ρ)≤T, counted with
multiplicity. Replacing this with only the critical-line count would assume
information not supplied by the unconditional Riemann–von Mangoldt formula.

For the full relevant Laplacian spectrum on the fixed finite-area arithmetic
surface, the frequency parameter t with λ=1/4+t² has a quadratic leading Weyl
term. N_ζ(T) instead has leading term T log T/(2π). Thus a direct ordered
identification of that entire spectrum with the zero heights fails this
counting test. The scattering poles are a different spectral object.
For the congruence-surface Weyl law, see [Müller, equation (1.9)](https://arxiv.org/pdf/2302.02207),
which states the quadratic main term and the lower-order cusp contribution.

This is not a theorem against every second-order differential operator,
against an explicitly constructed subsector with its own counting law, or
against arbitrary changes of spectral parameter. A candidate must specify its
space, operator, domain, spectral parameter, multiplicities, and counting law
before E12 applies. An unexplained rescaling is not an arithmetic identification.

## What the existing statements actually establish

`WeylOperatorChoice` and `WeylConfining` prove bounded-operator obstructions and
potential-shape facts. `ConfiningSpectralShape` packages obligations for a
discrete-spectrum candidate; its comments explicitly withhold essential
self-adjointness, compact resolvent and a zero-spectrum correspondence.
Compiling those modules does not fill the obligation structures.

The two counting schemas in `ConfiningSpectralShape` are definitions on
arbitrary functions. `EigenvalueCountingMatchesNT` requires the difference
of the counts to tend to zero; `EigenvalueCountingAsymptotic` requires their
ratio to tend to one. The former is far stronger than the latter. Neither is
instantiated there with a zeta counting function and a constructed operator.
For integer-valued counts, a difference tending to zero forces eventual
equality. Do not describe that schema as merely matching a leading asymptotic.

The weak-regularity and Kato–Rellich modules provide conditional analytic
implications and named remaining regularity/resolvent obligations. Their
compilation earns those implications. The operator question remains the
construction and arithmetic identification, with counting checked in the
chosen parameter. No RH-strength solver request follows from these repairs.
