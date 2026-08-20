import Mathlib
open Finset
namespace MS2.Probability
/-- Finite Markov inequality. The hypothesis `0 < a` is kept as stated, although the
proof does not need it (nonnegativity of `x` alone suffices). -/

theorem markov_finite {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (a : ℝ) (ha : 0 < a) :
    (a * (univ.filter (fun i => a ≤ x i)).card : ℝ) ≤ ∑ i, x i := by
  calc (a * (univ.filter (fun i => a ≤ x i)).card : ℝ)
      = ∑ _i ∈ univ.filter (fun i => a ≤ x i), a := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ univ.filter (fun i => a ≤ x i), x i :=
        Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i, x i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => hx i)

