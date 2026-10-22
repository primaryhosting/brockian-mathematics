# D5 operators and commuting rate comparisons

This focused extension connects the existing pentagon action and Fourier
decomposition to a classification of equivariant operators and a concrete
continuous-time rate comparison. The underlying representation theory and
commuting-semigroup argument are classical. The contribution here is an
explicit Lean integration with the repository's existing objects.

## Mathematical scope

`D5` has order ten. The specialized state space in this extension is the
**five vertices**, with uniform vector `(1/5, …, 1/5)`. It is not the ten-state
regular group walk in the Defant–Ono theorem.

Let `R` be the rotation pullback, `A₁ = R + R⁻¹`, and `A₂ = R² + R⁻²`.
Every complex-linear endomorphism commuting with the full vertex action
is uniquely `a I + b A₁ + c A₂`. Its real Markov Laplacians are exactly

\[
L=\alpha(2I-A_1)+\beta(2I-A_2),\qquad \alpha,\beta\ge0.
\]

The complete-graph term is redundant: `L₁ + L₂ = 5 I − J`.

More generally, pair the rates of inverse rotations and allow arbitrary
reflection rates `b k` on Mathlib's `sr k`. The pullback of `sr k` sends a
function value at `x` to its value at `−k−x`. With `ω = exp(2πi/5)`, put

\[
C_j(b)=\sum_{k\in\mathbb Z/5}b_k\omega^{jk}.
\]

For two such real rate collections, their vertex generators commute if and
only if

\[
\operatorname{Im}(C_j(b)\overline{C_j(d)})=0\quad(j=1,2).
\]

The condition includes zero symbols and opposite phases. It is an exact
criterion for **commutation**, and only a sufficient condition for the norm
comparison below. Arbitrary reflection rates need not give operators that
commute with the full D5 action; the name `D5EquivariantOperators.lean` does
not assert such equivariance for that larger class.

For a nonnegative base rate collection `λ` and a nonnegative increment `μ`
satisfying the two phase conditions, the concrete matrix semigroups obey

\[
\|e^{-tL_{\lambda+\mu}}v-u_5\|_p
\le\|e^{-tL_\lambda}v-u_5\|_p
\quad(t\ge0,\ 1\le p\le\infty).
\]

The finite-p norm uses counting measure and a real exponent. The infinity
case uses the supremum norm on real functions. The result holds for every
real vector `v`, hence every initial probability vector. It allows zero
rates, reducible chains, and time zero; it does not assert strict decrease
or uniqueness of the stationary distribution.

## Modules and main declarations

| Module | Purpose and principal declarations |
|---|---|
| `Brockian.D5Commutant` | Full complex-linear classification and actual-entry real Markov cone: `d5Equivariant_linear_exists_unique`, `d5Pull_markov_exists_unique`. |
| `Brockian.D5RateBlocks` | Hermitian two-by-two blocks, exact complex phase commutation, and scalar-shifted rate blocks. |
| `Brockian.D5EquivariantOperators` | Existing Fourier modes, exact block restriction, whole-vertex commutation, and real-coordinate action: `rateOperator_commute_iff_two`. Namespace `Brockian.D5RateOperators`. |
| `Brockian.D5MarkovContraction` | General finite balanced generators, positive doubly stochastic heat matrices, and all-p contraction under a commuting increment. Namespace `Brockian.MarkovContraction`. |
| `Brockian.D5RateComparison` | Explicit five-by-five rate matrix, balance, phase-to-matrix commutation, and the final theorem `markov_rate_comparison`. |
| `Brockian.D5Research` | Focused import target for the original D5 chain and this extension. |

The analytic module proves positivity of the matrix exponential by shifting
a matrix with nonnegative off-diagonal entries by a scalar identity. It
then proves preservation of constants and of total mass from the exponential
series. Jensen's inequality gives finite-p contraction; row sums give
supremum-norm contraction. Commuting exponentials factor the increased-rate
heat matrix, and preservation of constants gives the centered comparison.

## Reproduce the checks

Use the pinned `lean-toolchain` and `lake-manifest.json`; this extension does
not update dependencies. At the research baseline, Lean is 4.32.0 and Mathlib
is `81a5d257c8e410db227a6665ed08f64fea08e997`.

```sh
lake exe cache get
lake build Brockian.D5Research
lake env lean -DautoImplicit=false scripts/d5_axiom_audit.lean
python3 scripts/d5_source_manifest.py > d5-source-manifest.json
```

The axiom audit visits every theorem declared in the imported local
`Brockian` modules, follows transitive dependencies, and permits only
`propext`, `Classical.choice`, and `Quot.sound`. It also rejects project
axiom declarations. A `sorryAx` dependency or native decision oracle fails
the audit. The source manifest records the exact local import closure,
source hashes, toolchain, and dependency pins; it is not itself a build
verdict. See `D5_VALIDATION.md` for the recorded run.

The default whole-repository target is outside this check. No original
module is changed by the extension. Existing linter warnings should be
distinguished from proof errors.

## Boundaries and related work

The explicit hyperbolic-function block exponential, the group-to-vertex
quotient norm bound, the exact two-reflection counterexample, and a bundled
classification of all irreducible D5 representation objects are not
formalized by these new modules. They must not inherit the build status of
the statements actually checked here.

The new proofs neither establish historical mathematical novelty nor claim
to be the first formalization. The all-p result has a commutation hypothesis;
it is not globally stronger than the arbitrary-rate even-norm group theorem.

- Paul Garrett, [Harmonic analysis of dihedral groups](https://www-users.cse.umn.edu/~garrett/m/mfms/notes_c/dihedral.pdf), 29 May 2014.
- Peter J. Cameron, [Problems on Permutation Groups](https://webspace.maths.qmul.ac.uk/p.j.cameron/pgprob.html), orbital centralizer algebra discussion in Problem 8.
- Russell Lyons and Graham White, [Monotonicity for continuous-time random walks](https://rdlyons.pages.iu.edu/pdf/major-pub.pdf), Annals of Probability 51(3), 2023.
- Colin Defant and Ken Ono, [Proof of the Lyons–White Conjecture](https://arxiv.org/html/2608.27708v1), version 1, 27 August 2026.

Historical Aristotle/Harmonic attachments and stored AXLE verdicts are
separate provenance evidence. This extension's local Lean validation is
not a new AXLE or Aristotle service verdict.
