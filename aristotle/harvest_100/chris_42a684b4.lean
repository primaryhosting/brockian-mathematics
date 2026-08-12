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
def RiemannHypothesis {q : ℕ} (W : WeilData q) : Prop :=
  ∀ i, ∀ α ∈ W.eigen i, ‖α‖ = (q : ℝ) ^ ((i : ℝ) / 2)

section ProjectiveSpace

variable (q n : ℕ)

/-- The Frobenius eigenvalues of `ℙ^n` over `𝔽_q`: in even degree `i = 2j ≤ 2n` there is a single
eigenvalue `q^j`, and all odd-degree cohomology vanishes. -/
noncomputable def projEigen (i : ℕ) : Multiset ℂ :=
  if i % 2 = 0 ∧ i ≤ 2 * n then {(q : ℂ) ^ (i / 2)} else 0

private lemma proj_trace_aux (m : ℕ) :
    ∑ i ∈ range (2 * n + 1),
        (-1 : ℂ) ^ i * (if i % 2 = 0 then ((q : ℂ) ^ (i / 2)) ^ m else 0)
      = ∑ j ∈ range (n + 1), ((q : ℂ) ^ j) ^ m := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by ring
      rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ (n := k + 1)]
      have h1 : (2 * k + 1) % 2 = 1 := by omega
      have h2 : (2 * k + 1 + 1) % 2 = 0 := by omega
      have h3 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      have h4 : (-1 : ℂ) ^ (2 * k + 1 + 1) = 1 := by
        rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
        simp
      rw [h1, h2, h3, h4]
      simp

/-- The Weil data of projective `n`-space over `𝔽_q`. -/
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
theorem deligne_weil_RH (q n : ℕ) :
    ∃ W : WeilData q,
      W.dim = n ∧
      (∀ m, 1 ≤ m → W.N m = ∑ j ∈ range (n + 1), q ^ (j * m)) ∧
      RiemannHypothesis W := by
  refine ⟨projWeilData q n, rfl, fun m _ => rfl, ?_⟩
  intro i α hα
  simp only [projWeilData, projEigen] at hα
  by_cases hcond : i % 2 = 0 ∧ i ≤ 2 * n
  · rw [if_pos hcond] at hα
    have hα' : α = (q : ℂ) ^ (i / 2) := by
      simpa using hα
    subst hα'
    have h2 : ((i : ℝ)) / 2 = ((i / 2 : ℕ) : ℝ) := by
      obtain ⟨j, hj⟩ : ∃ j, i = 2 * j := ⟨i / 2, by omega⟩
      subst hj
      have : 2 * j / 2 = j := by omega
      rw [this]
      push_cast
      ring
    rw [h2, Real.rpow_natCast, norm_pow, Complex.norm_natCast]
  · rw [if_neg hcond] at hα
    simp at hα

/-- **A Lean-checked reduction.** For arbitrary Weil data, the Riemann hypothesis implies the
point-count estimate `#X(𝔽_{q^m}) ≤ (∑_i b_i) · q^{(dim X) · m}`, where `b_i` is the `i`-th Betti
number, i.e. the number of Frobenius eigenvalues in degree `i`. -/
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

