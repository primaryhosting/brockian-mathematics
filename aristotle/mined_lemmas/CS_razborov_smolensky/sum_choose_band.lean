import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/

theorem sum_choose_band (m D : ℕ) (hm : 1 ≤ m) :
    ∑ i ∈ Finset.range (m + D + 1), (2 * m).choose i
      ≤ 2 ^ (2 * m - 1) + (D + 1) * ((2 * m).choose m) := by
  have hsplit : ∑ i ∈ Finset.range m, (2 * m).choose i
      + ∑ i ∈ Finset.Ico m (m + D + 1), (2 * m).choose i
      = ∑ i ∈ Finset.range (m + D + 1), (2 * m).choose i :=
    Finset.sum_range_add_sum_Ico _ (by omega)
  have hlow : ∑ i ∈ Finset.range m, (2 * m).choose i ≤ 2 ^ (2 * m - 1) := by
    have h := sum_choose_halves m
    have hpow : 2 ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hhigh : ∑ i ∈ Finset.Ico m (m + D + 1), (2 * m).choose i
      ≤ (D + 1) * ((2 * m).choose m) := by
    have hbnd : ∀ i ∈ Finset.Ico m (m + D + 1), (2 * m).choose i ≤ (2 * m).choose m := by
      intro i _
      have := Nat.choose_le_middle i (2 * m)
      simpa [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] using this
    have := Finset.sum_le_card_nsmul _ _ _ hbnd
    simpa [Nat.card_Ico, smul_eq_mul, mul_comm, show m + D + 1 - m = D + 1 from by omega] using this
  omega

/-- Exponentials beat polynomials. -/
