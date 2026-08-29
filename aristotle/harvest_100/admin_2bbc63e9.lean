import Mathlib

/-!
# Eigenvalue Cauchy Schwarz Count
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- Auxiliary step: the "excess" `∑ ev i - θ·d` is bounded by the sum of the eigenvalues
that lie strictly above the threshold `θ` (eigenvalues below the threshold only help). -/
theorem excess_le_sum_above
    {d : ℕ} (ev : Fin d → ℝ) (theta : ℝ) (htheta : 0 ≤ theta) :
    (∑ i, ev i) - theta * d
      ≤ ∑ i ∈ Finset.univ.filter (fun i => theta < ev i), ev i := by
  have hd : ((d : ℝ)) = ((Finset.univ : Finset (Fin d)).card : ℝ) := by
    simp
  have hsplit :
      ∑ i, (ev i - theta)
        = (∑ i ∈ Finset.univ.filter (fun i => theta < ev i), (ev i - theta))
          + ∑ i ∈ Finset.univ.filter (fun i => ¬ theta < ev i), (ev i - theta) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hneg : ∑ i ∈ Finset.univ.filter (fun i => ¬ theta < ev i), (ev i - theta) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    simp only [Finset.mem_filter, not_lt] at hi
    linarith [hi.2]
  have hle : ∑ i ∈ Finset.univ.filter (fun i => theta < ev i), (ev i - theta)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => theta < ev i), ev i := by
    apply Finset.sum_le_sum
    intro i _
    linarith
  have hsum : ∑ i, (ev i - theta) = (∑ i, ev i) - theta * d := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  linarith [hsplit, hsum]

/-- Thresholded Cauchy–Schwarz count (Lemma 3.3) at the eigenvalue level:
if the total eigenvalue mass exceeds `θ·d`, then the squared excess is bounded by
the number of eigenvalues above `θ` times the sum of squares of all eigenvalues. -/
theorem eigenvalue_cauchy_schwarz_count
    {d : ℕ} (ev : Fin d → ℝ) (theta : ℝ) (htheta : 0 ≤ theta)
    (hsum : theta * d < ∑ i, ev i) :
    ((∑ i, ev i) - theta * d) ^ 2
      ≤ ((Finset.univ.filter (fun i => theta < ev i)).card : ℝ) * ∑ i, (ev i) ^ 2 := by
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hs
  have h1 : (∑ i, ev i) - theta * d ≤ ∑ i ∈ s, ev i := excess_le_sum_above ev theta htheta
  have h0 : (0:ℝ) < (∑ i, ev i) - theta * d := by linarith
  have hsq : ((∑ i, ev i) - theta * d) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := by
    apply pow_le_pow_left₀ (le_of_lt h0) h1
  have hcs : (∑ i ∈ s, ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hmono : ∑ i ∈ s, (ev i) ^ 2 ≤ ∑ i, (ev i) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    intro i _ _
    positivity
  have hcard : (0:ℝ) ≤ (s.card : ℝ) := by positivity
  calc ((∑ i, ev i) - theta * d) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := hsq
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 := hcs
    _ ≤ (s.card : ℝ) * ∑ i, (ev i) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hmono hcard

end Zeta23Redux.LinAlg

