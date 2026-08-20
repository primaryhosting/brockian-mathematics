import Mathlib
open Finset
namespace C4.Prob4

/-- AM–QM inequality. The nonnegativity hypothesis `hx` is part of the requested
statement, but it is not needed for the proof. -/

theorem am_qm {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hn : 0 < n) :
    (∑ i, x i)/n ≤ Real.sqrt ((∑ i, (x i)^2)/n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcs : (∑ i, x i) ^ 2 ≤ (n : ℝ) * ∑ i, (x i) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := x)
    simpa using this
  have key : ((∑ i, x i)/n) ^ 2 ≤ (∑ i, (x i)^2)/n := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hn']
    calc (∑ i, x i) ^ 2 * n ≤ ((n : ℝ) * ∑ i, (x i) ^ 2) * n := by
          exact mul_le_mul_of_nonneg_right hcs hn'.le
      _ = (∑ i, (x i) ^ 2) * (n : ℝ) ^ 2 := by ring
  calc (∑ i, x i)/n ≤ |(∑ i, x i)/n| := le_abs_self _
    _ = Real.sqrt (((∑ i, x i)/n) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, (x i)^2)/n) := Real.sqrt_le_sqrt key

