# Research routes and reopening conditions

16 September 2026. Status refers to the available source and receipts in this
review branch. Reported v5 pilots are not substituted for missing build evidence.

| Route | Status | What survives | Gate for additional RH-directed work |
|---|---|---|---|
| E18: prime-level Fricke channels | Algebra under kernel review; analytic transfer conditional | Exact rational factors, determinant, C₂ projectors, regular-domain functional equations | Pin analytic input and prove any claimed pole order, including cancellations |
| E19: holonomy and observers | General observer proof under kernel review; full determinant formalization open | Quotient observer invariant, loop return order, written cycle classification | Compile the one-step cycle decomposition and determinant theorem |
| E20/E01: shared finite Fourier structure | Generic theorem under kernel review | Orthogonality, complete cyclic projectors, dihedral relation, Hückel eigenmodes for all N>0 | Add bridges into existing D₅ consumers and certify polynomial/rank corollaries |
| E21: finite-field template | Complete written conditional-on-classical-input proof | Exact location of the geometric sign and full Gram calculation | Arithmetic candidate must fill all six roles in FINITE_FIELD_TEMPLATE.md |
| Spec Z / Picard monoid | SIGN_GATE_UNMET | Concrete arithmetic moduli and semilocal trace geometry | Independent primitive pairing and index/sign theorem, with the global limiting bridge |
| Li / Laguerre discrepancy | PARKED | Generating-function identity, exact rate dictionary, verification-height bound, E16/E17 tools | A new independent structural input, or a demonstrated error in the stated dictionary or its hypotheses |
| Full Laplacian spectrum of Y₀(5) | CONTROL; no direct counting identification | Scattering/resonance interpretation and ordinary spectral theory | A precise different spectral object, with its own counting theorem and arithmetic identification |
| Berry–Keating xp | OPEN MODEL | Semiclassical shape heuristic | Defined operator/domain, spectral counting, prime terms, identification theorem |
| Connes adelic spectral approach | POSITIVITY OPEN | Trace/spectral realization results with their stated functional-analytic scope | A new positivity theorem; relabelling an RH-equivalent condition does not count |
| Fitted Schrödinger model | CALIBRATION ONLY | A finite fitted spectrum | An independent infinite arithmetic identification and a tail/counting theorem |
| Lax–Phillips scattering | OPEN TRANSFER | Resonance realization by an appropriate non-self-adjoint generator | A structural constraint on arithmetic resonances, not an assumption of self-adjointness |

## Li route: exact statement retained

Use H(s)=(s−1)ζ(s), H(1)=1, and the analytic germ

\[
-H'(1+t)/H(1+t)=\sum_{j\ge0}\eta_jt^j,
\quad S_f(n)=\sum_{j=1}^n {n\choose j}\eta_{j-1}.
\]

With this normalization S_f(1)=−γ. Summing the binomial transform locally gives

\[
G(z)=\sum_{n\ge1}S_f(n)z^n
=-\frac{z}{(1-z)^2}\frac{H'(1/(1-z))}{H(1/(1-z))}.
\tag{L1}
\]

This is a locally convergent identity first, followed by meromorphic continuation.
For a nontrivial zero ρ of multiplicity m, z_ρ=1−1/ρ is a genuine pole of G
with residue −m z_ρ. The map is injective, z_ρ≠0, and distinct zero locations
cannot cancel each other's poles. Also |z_ρ|<1 iff Re(ρ)>1/2.

Together with the classical functional-equation symmetry and zero location,
Cauchy–Hadamard gives

\[
\sigma_f:=\limsup_{n\to\infty}\frac{\log(1+|S_f(n)|)}{n}
=\max\left(0,\sup_\rho\log\left|\frac{\rho}{\rho-1}\right|\right).
\tag{L2}
\]

If the supremum is positive it is attained at finite height: its contribution
tends uniformly to zero as |Im(ρ)|→∞ while 0<Re(ρ)<1. This does not mean the
lowest zero necessarily dominates; displacement from the line also matters.
In particular σ_f=0 is equivalent to RH. This is a written analytic deduction,
not a newly compiled Lean theorem or a novelty claim. For related Li-coefficient
analysis and conditional estimates see [Lagarias](https://arxiv.org/pdf/math/0404394).

## The unconditional band and what an improvement would say

If every nontrivial zero with |Im(ρ)|≤T is on the line, then

\[
0\le\sigma_f\le\delta_T:=\tfrac12\log(1+T^{-2}).
\tag{L3}
\]

Indeed for ρ=β+iγ with β>1/2 and |γ|>T,

\[
\left|\frac{\rho}{\rho-1}\right|^2
=1+\frac{2\beta-1}{(1-\beta)^2+\gamma^2}\le1+T^{-2}.
\]

The published certified verification of [Platt–Trudgian](https://arxiv.org/abs/2004.09765)
allows T=3·10¹². That is a sufficient cited baseline here, not a claim about
the latest available verification height. The bound is strictly positive.
It cannot be rounded to zero in a proof.

**Precise prediction.** A valid unconditional improvement σ_f≤c<δ_T excludes
zeros in the region

\[
\frac12\log\frac{\beta^2+\gamma^2}{(1-\beta)^2+\gamma^2}>c.
\tag{L4}
\]

Any still-undecided zeros in that region lie above T. A positive c does not
exclude every off-line zero at arbitrarily large height. Beating the coarse
bound δ_T may also merely recover information already supplied by a sharper
zero-free region. Compare the actual excluded region before claiming progress.
An unrestricted statement that there is "no intermediate range" is withdrawn:
the rate dictionary admits a continuum of positive rates.

## Tail and reopening discipline

The retained prime-side identity is

\[
S_f(n)=\lim_{X\to\infty}\left[
\sum_{m\le X}\frac{\Lambda(m)}m L_{n-1}^{(1)}(\log m)
-\int_0^{\log X}L_{n-1}^{(1)}(u)\,du\right].
\]

The fixed-n limit and the uniform-in-n estimate are different obligations.
E16/E17 remain tools for exact normalization and certified tail handling;
they are not assigned an RH-evidence badge. No individual-prime absolute bound
is summed over all primes without a convergence argument. No new solver jobs
are sent on the subexponential bound or its RH-equivalent variants.

Reopening requires a written lemma with independent hypotheses, its precise
arithmetic use, uniform tail control, and a noncircular treatment of poles.
A counterexample to an overbroad slogan can correct the slogan; it cannot
refute the correctly stated analytic equivalence. Additional finite positive
Li coefficients do not meet this gate.
