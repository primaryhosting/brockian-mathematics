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

theorem huckel_C8 (μ : ℝ) :
    (∃ v : Fin 8 → ℝ, v ≠ 0 ∧ C8adj *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 8 ∧ μ = 2 * Real.cos (2 * Real.pi * (k : ℝ) / 8) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    have h : ∀ i : Fin 8, v (i - 1) + v (i + 1) = μ * v i := by
      intro i
      rw [← C8adj_mulVec, hv]
      rfl
    have hne : ¬ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 ∧ v 6 = 0 ∧
        v 7 = 0) := by
      rintro ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
      refine hv0 (funext fun i => ?_)
      fin_cases i
      · exact a0
      · exact a1
      · exact a2
      · exact a3
      · exact a4
      · exact a5
      · exact a6
      · exact a7
    have hroot : μ ^ 5 - 6 * μ ^ 3 + 8 * μ = 0 :=
      quintic_root_of_cyclic_relation μ (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
        (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) hne
    have hfac : μ * ((μ ^ 2 - 2) * (μ ^ 2 - 4)) = 0 := by linarith [hroot, sq_nonneg μ]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := sqrt_two_sq
    rcases mul_eq_zero.1 hfac with hμ | hrest
    · exact ⟨2, by norm_num, by rw [cos_val_2, hμ]⟩
    rcases mul_eq_zero.1 hrest with hμ | hμ
    · have : (μ - Real.sqrt 2) * (μ + Real.sqrt 2) = 0 := by nlinarith [hμ, h2]
      rcases mul_eq_zero.1 this with h' | h'
      · exact ⟨1, by norm_num, by rw [cos_val_1]; linarith⟩
      · exact ⟨3, by norm_num, by rw [cos_val_3]; linarith⟩
    · have : (μ - 2) * (μ + 2) = 0 := by nlinarith [hμ]
      rcases mul_eq_zero.1 this with h' | h'
      · exact ⟨0, by norm_num, by rw [cos_val_0]; linarith⟩
      · exact ⟨4, by norm_num, by rw [cos_val_4]; linarith⟩
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · rw [cos_val_0]; exact eigen_two
    · rw [cos_val_1]; exact eigen_sqrt_two
    · rw [cos_val_2]; exact eigen_zero
    · rw [cos_val_3]; exact eigen_neg_sqrt_two
    · rw [cos_val_4]; exact eigen_neg_two
    · rw [cos_val_5]; exact eigen_neg_sqrt_two
    · rw [cos_val_6]; exact eigen_zero
    · rw [cos_val_7]; exact eigen_sqrt_two

/-! ### The characteristic polynomial, i.e. the eigenvalues with multiplicities

We diagonalise the adjacency matrix over `ℂ` using the discrete Fourier (Vandermonde) matrix
built from a primitive `8`-th root of unity. -/

/-- A primitive eighth root of unity. -/
