import Mathlib
open Finset
namespace Frontier.InformationTheory

theorem gibbs_nonneg {n : ℕ} (p q : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hsp : ∑ i, p i = 1) (hsq : ∑ i, q i = 1) : 0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  have key : ∀ i : Fin n, p i - q i ≤ p i * Real.log (p i / q i) := by
    intro i
    have hpi := hp i
    have hqi := hq i
    have hlog : Real.log (q i / p i) ≤ q i / p i - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hqi hpi)
    have hmul : p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) :=
      mul_le_mul_of_nonneg_left hlog hpi.le
    have hrw : p i * (q i / p i - 1) = q i - p i := by
      field_simp
    have hneg : Real.log (q i / p i) = - Real.log (p i / q i) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [hneg, hrw] at hmul
    linarith
  have hsum : ∑ i, (p i - q i) ≤ ∑ i, p i * Real.log (p i / q i) :=
    Finset.sum_le_sum (fun i _ => key i)
  rw [Finset.sum_sub_distrib, hsp, hsq] at hsum
  simpa using hsum

end Frontier.InformationTheory

