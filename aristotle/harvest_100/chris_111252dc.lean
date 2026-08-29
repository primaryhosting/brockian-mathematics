/-!
# Eigenvalue Cauchy Schwarz Count

Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- The total sum of the eigenvalues minus `θ * d` is bounded by the sum of the
eigenvalues exceeding `θ`: the entries below the threshold contribute a nonpositive
amount, and `θ ≥ 0` lets us drop the `θ` shift on the remaining entries. -/
lemma sum_sub_le_sum_filter {d : ℕ} (ev : Fin d → ℝ) {theta : ℝ} (htheta : 0 ≤ theta) :
    (∑ i, ev i) - theta * d ≤
      ∑ i ∈ Finset.univ.filter (fun i => theta < ev i), ev i := by
  classical
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hs
  have hsplit : (∑ i, (ev i - theta)) =
      (∑ i ∈ s, (ev i - theta)) + ∑ i ∈ sᶜ, (ev i - theta) := by
    rw [← Finset.sum_add_sum_compl s (fun i => ev i - theta)]
  have hcompl : ∑ i ∈ sᶜ, (ev i - theta) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro i hi
    have : ¬ theta < ev i := by
      simpa [hs, Finset.mem_compl, Finset.mem_filter] using hi
    linarith [not_lt.mp this]
  have h1 : (∑ i, (ev i - theta)) ≤ ∑ i ∈ s, (ev i - theta) := by
    rw [hsplit]; linarith
  have h2 : ∑ i ∈ s, (ev i - theta) = (∑ i ∈ s, ev i) - s.card * theta := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  have h3 : (0:ℝ) ≤ s.card * theta := by positivity
  have h4 : (∑ i, (ev i - theta)) = (∑ i, ev i) - theta * d := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  linarith [h1, h2.le, h2.ge, h3, h4.le, h4.ge]

/-- **Thresholded Cauchy–Schwarz count** (Lemma 3.3 at the eigenvalue level).
If `θ ≥ 0` and the eigenvalue sum exceeds `θ * d`, then
`(∑ ev - θ d)² ≤ n * ∑ ev²`, where `n` is the number of eigenvalues above `θ`. -/
theorem eigenvalue_cauchy_schwarz_count
    (d : ℕ) (ev : Fin d → ℝ) (theta : ℝ) (htheta : 0 ≤ theta)
    (s : Finset (Fin d)) (hs : s = Finset.univ.filter (fun i => theta < ev i))
    (n : ℕ) (hn : n = s.card)
    (hsum : theta * d < ∑ i, ev i) :
    ((∑ i, ev i) - theta * d) ^ 2 ≤ (n : ℝ) * ∑ i, (ev i) ^ 2 := by
  classical
  subst hs hn
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hsdef
  have hle : (∑ i, ev i) - theta * d ≤ ∑ i ∈ s, ev i :=
    sum_sub_le_sum_filter ev htheta
  have hpos : 0 < (∑ i, ev i) - theta * d := by linarith
  have hsq : ((∑ i, ev i) - theta * d) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := by
    apply pow_le_pow_left₀ (le_of_lt hpos) hle
  have hcs : (∑ i ∈ s, ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 :=
    Finset.sq_sum_le_card_mul_sum_sq
  have hsub : ∑ i ∈ s, (ev i) ^ 2 ≤ ∑ i, (ev i) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) ?_
    intro i _ _
    positivity
  have hcard : (0:ℝ) ≤ (s.card : ℝ) := by positivity
  calc ((∑ i, ev i) - theta * d) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := hsq
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 := hcs
    _ ≤ (s.card : ℝ) * ∑ i, (ev i) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsub hcard

end Zeta23Redux.LinAlg

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

