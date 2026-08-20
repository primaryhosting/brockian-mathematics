import Mathlib

open Finset Polynomial ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Math

/-- The sum of all `n`-th roots of unity in `ℂ` is `0`, for `1 < n`. -/

theorem mobius_root_sum_9 : ∑ ζ ∈ primitiveRoots 9 ℂ, ζ = (μ 9 : ℂ) := by
  have h9 : ∑ d ∈ (9 : ℕ).divisors, ∑ ζ ∈ primitiveRoots d ℂ, ζ = 0 := by
    rw [sum_divisors_sum_primitiveRoots]
    exact sum_nthRootsFinset_eq_zero (by norm_num)
  have h3 : ∑ d ∈ (3 : ℕ).divisors, ∑ ζ ∈ primitiveRoots d ℂ, ζ = 0 := by
    rw [sum_divisors_sum_primitiveRoots]
    exact sum_nthRootsFinset_eq_zero (by norm_num)
  have e9 : (9 : ℕ).divisors = {1, 3, 9} := by decide
  have e3 : (3 : ℕ).divisors = {1, 3} := by decide
  rw [e9] at h9
  rw [e3] at h3
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at h9
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h3
  have hmu : (μ 9 : ℂ) = 0 := by
    have hns : ¬ Squarefree (9 : ℕ) := by
      intro h
      have h3 := h 3 ⟨1, by norm_num⟩
      rw [Nat.isUnit_iff] at h3
      omega
    have : μ 9 = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns
    rw [this]
    norm_num
  rw [hmu]
  linear_combination h9 - h3

end Math

