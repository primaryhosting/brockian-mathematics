import Mathlib
/-!
# Eigenvalue Cauchy Schwarz Count
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Zeta23Redux
namespace LinAlg

/-- **Thresholded Cauchy–Schwarz count (Lemma 3.3, eigenvalue level).**
Given eigenvalues `ev : Fin d → ℝ` and a threshold `theta ≥ 0` such that
`theta * d < ∑ i, ev i`, the number `n` of eigenvalues exceeding `theta`
satisfies `(∑ i, ev i - theta * d)^2 ≤ n * ∑ i, (ev i)^2`. -/
theorem eigenvalue_cauchy_schwarz_count
    (d : ℕ) (ev : Fin d → ℝ) (theta : ℝ) (htheta : 0 ≤ theta)
    (hsum : theta * (d : ℝ) < ∑ i, ev i) :
    ((∑ i, ev i) - theta * (d : ℝ)) ^ 2
      ≤ (((Finset.univ.filter (fun i => theta < ev i)).card : ℕ) : ℝ)
          * ∑ i, (ev i) ^ 2 := by
  classical
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hs
  -- the total shifted sum equals the sum of `ev i - theta`
  have hshift : (∑ i, ev i) - theta * (d : ℝ) = ∑ i, (ev i - theta) := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  -- split the shifted sum along the threshold
  have hsplit :
      (∑ i ∈ s, (ev i - theta))
        + ∑ i ∈ Finset.univ.filter (fun i => ¬ theta < ev i), (ev i - theta)
      = ∑ i, (ev i - theta) :=
    Finset.sum_filter_add_sum_filter_not Finset.univ _ _
  have hnonpos :
      ∑ i ∈ Finset.univ.filter (fun i => ¬ theta < ev i), (ev i - theta) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro i hi
    simp only [Finset.mem_filter, not_lt] at hi
    linarith [hi.2]
  -- hence the shifted sum is at most the sum over the "large" eigenvalues
  have hle1 : (∑ i, ev i) - theta * (d : ℝ) ≤ ∑ i ∈ s, ev i := by
    have hcard : (0 : ℝ) ≤ (s.card : ℝ) * theta :=
      mul_nonneg (Nat.cast_nonneg _) htheta
    have hsub : ∑ i ∈ s, (ev i - theta) = (∑ i ∈ s, ev i) - (s.card : ℝ) * theta := by
      rw [Finset.sum_sub_distrib]
      simp [mul_comm]
    rw [hshift, ← hsplit, hsub]
    linarith
  have hpos : (0 : ℝ) ≤ (∑ i, ev i) - theta * (d : ℝ) := by linarith
  -- Cauchy–Schwarz on the "large" eigenvalues
  have hcs : (∑ i ∈ s, ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsq : ∑ i ∈ s, (ev i) ^ 2 ≤ ∑ i, (ev i) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => sq_nonneg _)
  have hmono : ((∑ i, ev i) - theta * (d : ℝ)) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 :=
    pow_le_pow_left₀ hpos hle1 2
  have hfin : (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i, (ev i) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
  linarith

end LinAlg
end Zeta23Redux

