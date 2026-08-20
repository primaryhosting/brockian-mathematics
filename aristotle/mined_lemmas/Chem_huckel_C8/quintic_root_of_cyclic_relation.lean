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

set_option grind.warning false

namespace Chem

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₈`. -/

lemma quintic_root_of_cyclic_relation (m c0 c1 c2 c3 c4 c5 c6 c7 : ℝ)
    (h0 : c7 + c1 = m * c0) (h1 : c0 + c2 = m * c1) (h2 : c1 + c3 = m * c2)
    (h3 : c2 + c4 = m * c3) (h4 : c3 + c5 = m * c4) (h5 : c4 + c6 = m * c5)
    (h6 : c5 + c7 = m * c6) (h7 : c6 + c0 = m * c7)
    (hne : ¬ (c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 ∧ c7 = 0)) :
    m ^ 5 - 6 * m ^ 3 + 8 * m = 0 := by
  have q0 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c0 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h0 + (-(m ^ 3 - 3 * m)) * h1 +
      (-(m ^ 3 - 3 * m)) * h7 + (-(m ^ 2 - 2)) * h2 + (-(m ^ 2 - 2)) * h6 + (-m) * h3 +
      (-m) * h5 + (-2 : ℝ) * h4
  have q1 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c1 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h1 + (-(m ^ 3 - 3 * m)) * h2 +
      (-(m ^ 3 - 3 * m)) * h0 + (-(m ^ 2 - 2)) * h3 + (-(m ^ 2 - 2)) * h7 + (-m) * h4 +
      (-m) * h6 + (-2 : ℝ) * h5
  have q2 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c2 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h2 + (-(m ^ 3 - 3 * m)) * h3 +
      (-(m ^ 3 - 3 * m)) * h1 + (-(m ^ 2 - 2)) * h4 + (-(m ^ 2 - 2)) * h0 + (-m) * h5 +
      (-m) * h7 + (-2 : ℝ) * h6
  have q3 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c3 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h3 + (-(m ^ 3 - 3 * m)) * h4 +
      (-(m ^ 3 - 3 * m)) * h2 + (-(m ^ 2 - 2)) * h5 + (-(m ^ 2 - 2)) * h1 + (-m) * h6 +
      (-m) * h0 + (-2 : ℝ) * h7
  have q4 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c4 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h4 + (-(m ^ 3 - 3 * m)) * h5 +
      (-(m ^ 3 - 3 * m)) * h3 + (-(m ^ 2 - 2)) * h6 + (-(m ^ 2 - 2)) * h2 + (-m) * h7 +
      (-m) * h1 + (-2 : ℝ) * h0
  have q5 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c5 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h5 + (-(m ^ 3 - 3 * m)) * h6 +
      (-(m ^ 3 - 3 * m)) * h4 + (-(m ^ 2 - 2)) * h7 + (-(m ^ 2 - 2)) * h3 + (-m) * h0 +
      (-m) * h2 + (-2 : ℝ) * h1
  have q6 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c6 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h6 + (-(m ^ 3 - 3 * m)) * h7 +
      (-(m ^ 3 - 3 * m)) * h5 + (-(m ^ 2 - 2)) * h0 + (-(m ^ 2 - 2)) * h4 + (-m) * h1 +
      (-m) * h3 + (-2 : ℝ) * h2
  have q7 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c7 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h7 + (-(m ^ 3 - 3 * m)) * h0 +
      (-(m ^ 3 - 3 * m)) * h6 + (-(m ^ 2 - 2)) * h1 + (-(m ^ 2 - 2)) * h5 + (-m) * h2 +
      (-m) * h4 + (-2 : ℝ) * h3
  push_neg at hne
  by_contra hm
  refine hne ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    [exact (mul_eq_zero.1 q0).resolve_left hm;
     exact (mul_eq_zero.1 q1).resolve_left hm;
     exact (mul_eq_zero.1 q2).resolve_left hm;
     exact (mul_eq_zero.1 q3).resolve_left hm;
     exact (mul_eq_zero.1 q4).resolve_left hm;
     exact (mul_eq_zero.1 q5).resolve_left hm;
     exact (mul_eq_zero.1 q6).resolve_left hm;
     exact (mul_eq_zero.1 q7).resolve_left hm]

/-- **Hückel theory for cyclic C₈ (cyclooctatetraene).**  A real number `μ` is an eigenvalue of
the adjacency matrix of the cycle graph `C₈` if and only if `μ = 2 cos (2πk/8)` for some
`k ∈ {0, 1, …, 7}`. -/
