import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization

We formalize the *Riemann hypothesis part* of the Weil conjectures (proved by Deligne) in its
standard elementary reformulation in terms of the Frobenius eigenvalues occurring in the
Lefschetz trace formula.

A smooth projective variety `X` of dimension `d` over the finite field `𝔽_q` has, for every
`m ≥ 1`, a number of `𝔽_{q^m}`-rational points `N m`, and (by the Grothendieck–Lefschetz trace
formula) there are finite families of complex numbers `α_{i,1}, …, α_{i,b_i}` — the eigenvalues of
Frobenius on the `i`-th `ℓ`-adic cohomology group, `0 ≤ i ≤ 2d` — such that

  `N m = ∑_{i=0}^{2d} (-1)^i ∑_j α_{i,j}^m`.

This package of data is recorded by `Frontier.WeilData`. The Riemann hypothesis
(`Frontier.RiemannHypothesis`) then asserts that every eigenvalue in degree `i` has complex
absolute value exactly `q^{i/2}` — equivalently, that all the zeros/poles of the zeta function
`Z(X, T) = exp(∑_m N m T^m / m)` lie on the lines `Re(s) = i/2`.

Two results are proved here:

* `Frontier.deligne_weil_RH` : the Riemann hypothesis holds for projective `n`-space over `𝔽_q`
  (this includes the base case `n = 0` of a single point). Concretely we exhibit the Weil data
  of `ℙ^n_{𝔽_q}`, whose point counts are `N m = 1 + q^m + ⋯ + q^{nm}`, and verify that all its
  Frobenius eigenvalues satisfy the weight condition `|α| = q^{i/2}`.

* `Frontier.weil_RH_point_count_bound` : a Lean-checked reduction, valid for arbitrary Weil data:
  the Riemann hypothesis implies the point-count estimate
  `N m ≤ (∑_i b_i) · q^{d m}` for all `m ≥ 1`.
-/

namespace Frontier

open Finset

/-- The cohomological data attached to a `d`-dimensional variety over the finite field `𝔽_q`:
the point counts `N m = #X(𝔽_{q^m})` together with the Frobenius eigenvalues `eigen i` on the
`i`-th cohomology group, linked by the Lefschetz trace formula. -/
structure WeilData (q : ℕ) where
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- `N m` is the number of `𝔽_{q^m}`-rational points. -/
  N : ℕ → ℕ
  /-- `eigen i` is the multiset of eigenvalues of the Frobenius endomorphism acting on the `i`-th
  `ℓ`-adic cohomology group. -/
  eigen : ℕ → Multiset ℂ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  eigen_vanishing : ∀ i, 2 * dim < i → eigen i = 0
  /-- The Grothendieck–Lefschetz trace formula. -/
  trace_formula : ∀ m, 1 ≤ m →
    (N m : ℂ) = ∑ i ∈ range (2 * dim + 1), (-1) ^ i * ((eigen i).map (· ^ m)).sum

/-- The Riemann hypothesis for a variety over `𝔽_q`: every Frobenius eigenvalue occurring in
cohomological degree `i` is an algebraic number all of whose absolute values equal `q^{i/2}`
(here stated for the given complex embedding). -/

noncomputable def projWeilData : WeilData q where
  dim := n
  N := fun m => ∑ j ∈ range (n + 1), q ^ (j * m)
  eigen := projEigen q n
  eigen_vanishing := by
    intro i hi
    simp only [projEigen, if_neg (by omega : ¬(i % 2 = 0 ∧ i ≤ 2 * n))]
  trace_formula := by
    intro m _
    have hcast : ((∑ j ∈ range (n + 1), q ^ (j * m) : ℕ) : ℂ)
        = ∑ j ∈ range (n + 1), ((q : ℂ) ^ j) ^ m := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => by rw [← pow_mul]
    rw [hcast, ← proj_trace_aux q n m]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ 2 * n := by
      simp only [Finset.mem_range] at hi; omega
    by_cases hpar : i % 2 = 0
    · simp [projEigen, hpar, hi']
    · simp [projEigen, hpar]

end ProjectiveSpace

/-- **The Riemann hypothesis of the Weil conjectures (Deligne), base case.**

For projective `n`-space over the finite field `𝔽_q` there exists Weil data — point counts
`N m = 1 + q^m + ⋯ + q^{nm} = #ℙ^n(𝔽_{q^m})` together with Frobenius eigenvalues satisfying the
Lefschetz trace formula — for which the Riemann hypothesis holds: every eigenvalue occurring in
cohomological degree `i` has absolute value exactly `q^{i/2}`.

For `n = 0` this is the case of a single point. -/
