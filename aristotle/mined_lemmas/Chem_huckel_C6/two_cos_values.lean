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

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/

lemma two_cos_values (μ : ℝ) :
    (∃ k ∈ Finset.range 6, μ = 2 * Real.cos (2 * Real.pi * k / 6)) ↔
      (μ = 2 ∨ μ = 1 ∨ μ = -1 ∨ μ = -2) := by
  have h1 : Real.cos (2 * Real.pi * (1 : ℕ) / 6) = 1 / 2 := by
    rw [show (2 * Real.pi * (1 : ℕ) / 6 : ℝ) = Real.pi / 3 by push_cast; ring]
    exact Real.cos_pi_div_three
  have h2 : Real.cos (2 * Real.pi * (2 : ℕ) / 6) = -(1 / 2) := by
    rw [show (2 * Real.pi * (2 : ℕ) / 6 : ℝ) = Real.pi - Real.pi / 3 by push_cast; ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  have h3 : Real.cos (2 * Real.pi * (3 : ℕ) / 6) = -1 := by
    rw [show (2 * Real.pi * (3 : ℕ) / 6 : ℝ) = Real.pi by push_cast; ring, Real.cos_pi]
  have h4 : Real.cos (2 * Real.pi * (4 : ℕ) / 6) = -(1 / 2) := by
    rw [show (2 * Real.pi * (4 : ℕ) / 6 : ℝ) = Real.pi / 3 + Real.pi by push_cast; ring,
      Real.cos_add_pi, Real.cos_pi_div_three]
  have h5 : Real.cos (2 * Real.pi * (5 : ℕ) / 6) = 1 / 2 := by
    rw [show (2 * Real.pi * (5 : ℕ) / 6 : ℝ) = 2 * Real.pi - Real.pi / 3 by push_cast; ring,
      Real.cos_two_pi_sub, Real.cos_pi_div_three]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk
    interval_cases k
    · norm_num
    · rw [h1]; norm_num
    · rw [h2]; norm_num
    · rw [h3]; norm_num
    · rw [h4]; norm_num
    · rw [h5]; norm_num
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp, by norm_num⟩
    · exact ⟨1, by simp, by rw [h1]; norm_num⟩
    · exact ⟨2, by simp, by rw [h2]; norm_num⟩
    · exact ⟨3, by simp, by rw [h3]; norm_num⟩

/-- Explicit eigenvectors: for each of `2, 1, -1, -2` there is a nonzero eigenvector. -/
