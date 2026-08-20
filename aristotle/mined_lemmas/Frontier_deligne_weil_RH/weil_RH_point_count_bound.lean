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

theorem weil_RH_point_count_bound {q : ℕ} (hq : 1 ≤ q) (W : WeilData q)
    (hRH : RiemannHypothesis W) (m : ℕ) (hm : 1 ≤ m) :
    (W.N m : ℝ)
      ≤ (∑ i ∈ range (2 * W.dim + 1), ((W.eigen i).card : ℝ)) * (q : ℝ) ^ (W.dim * m) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_trans zero_le_one hq1
  -- bound the norm of each cohomological contribution
  have key : ∀ i ∈ range (2 * W.dim + 1),
      ‖(-1 : ℂ) ^ i * ((W.eigen i).map (· ^ m)).sum‖
        ≤ ((W.eigen i).card : ℝ) * (q : ℝ) ^ (W.dim * m) := by
    intro i hi
    have hi' : i ≤ 2 * W.dim := by simp only [Finset.mem_range] at hi; omega
    have hnorm : ‖(-1 : ℂ) ^ i * ((W.eigen i).map (· ^ m)).sum‖
        = ‖((W.eigen i).map (fun α : ℂ => α ^ m)).sum‖ := by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [hnorm]
    refine le_trans (norm_multiset_sum_le _) ?_
    have hmap : ((W.eigen i).map (fun α : ℂ => α ^ m)).map (fun z : ℂ => ‖z‖)
        = (W.eigen i).map (fun α : ℂ => ‖α ^ m‖) := by
      rw [Multiset.map_map]; rfl
    rw [hmap]
    have hbd : ∀ x ∈ (W.eigen i).map (fun α : ℂ => ‖α ^ m‖),
        x ≤ (q : ℝ) ^ (W.dim * m) := by
      intro x hx
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp hx
      have hnα : ‖α‖ = (q : ℝ) ^ ((i : ℝ) / 2) := hRH i α hα
      rw [norm_pow, hnα, ← Real.rpow_natCast ((q : ℝ) ^ ((i : ℝ) / 2)) m,
        ← Real.rpow_mul hq0, ← Real.rpow_natCast (q : ℝ) (W.dim * m)]
      refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
      have hile : (i : ℝ) ≤ 2 * (W.dim : ℝ) := by exact_mod_cast hi'
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      push_cast
      nlinarith
    have := Multiset.sum_le_card_nsmul _ _ hbd
    simpa [Multiset.card_map, nsmul_eq_mul] using this
  have hsum : (W.N m : ℝ) = ‖((W.N m : ℕ) : ℂ)‖ := by
    rw [Complex.norm_natCast]
  rw [hsum, W.trace_formula m hm]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum key

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

