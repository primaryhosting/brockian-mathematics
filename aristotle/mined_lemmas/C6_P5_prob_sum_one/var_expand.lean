import Mathlib
open Finset
namespace C6.P5

theorem var_expand {n : ℕ} (x : Fin n → ℝ) (m : ℝ) :
    ∑ i, (x i - m)^2 = (∑ i, (x i)^2) - 2*m*(∑ i, x i) + n*m^2 := by
  have h : ∀ i, (x i - m)^2 = (x i)^2 - (2*m) * x i + m^2 := fun i => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

