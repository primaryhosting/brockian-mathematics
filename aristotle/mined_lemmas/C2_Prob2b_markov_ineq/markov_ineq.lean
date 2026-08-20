import Mathlib
open Finset
namespace C2.Prob2b

/-- Markov's inequality (counting form): for nonnegative reals `x i`,
`a` times the number of indices with `a ≤ x i` is at most `∑ i, x i`.
The hypothesis `0 < a` turns out to be unnecessary for the proof. -/

theorem markov_ineq {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (a : ℝ) (ha : 0 < a) :
    (a * ((univ.filter (fun i => a ≤ x i)).card) : ℝ) ≤ ∑ i, x i := by
  classical
  have h1 : (a * ((univ.filter (fun i => a ≤ x i)).card) : ℝ)
      = ∑ _i ∈ univ.filter (fun i => a ≤ x i), a := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [h1]
  calc ∑ _i ∈ univ.filter (fun i => a ≤ x i), a
      ≤ ∑ i ∈ univ.filter (fun i => a ≤ x i), x i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        simpa using (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, x i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => hx i)

/-- Jensen's inequality for a finite average: a convex function of the mean is at most
the mean of the values. -/
