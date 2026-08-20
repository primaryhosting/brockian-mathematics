import Mathlib

/-!
# Hückel theory for the cyclic polyene C₁₂

The adjacency eigenvalues of the cycle graph `C₁₂` are `2 * cos (2 * π * k / 12)` for
`k = 0, …, 11`.
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Polynomial Matrix

/-- A primitive 12-th root of unity. -/

lemma zeta_add_zeta_neg (k : Fin 12) :
    zeta k + zeta (-k) = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 12) : ℝ) : ℂ) := by
  have hinv : zeta (-k) = Complex.exp (-((2 * Real.pi * (k : ℕ) / 12 : ℝ) : ℂ) * Complex.I) := by
    have h := zeta_neg_mul k
    rw [zeta_eq_exp k] at h
    have : Complex.exp (((2 * Real.pi * (k : ℕ) / 12 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((2 * Real.pi * (k : ℕ) / 12 : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      simp
    have hne : Complex.exp (((2 * Real.pi * (k : ℕ) / 12 : ℝ) : ℂ) * Complex.I) ≠ 0 :=
      Complex.exp_ne_zero _
    field_simp at h this ⊢
    exact mul_left_cancel₀ hne (h.trans this.symm)
  rw [zeta_eq_exp k, hinv, ← Complex.two_cos]
  push_cast
  ring

/-- The (complex) adjacency matrix of the 12-cycle. -/
