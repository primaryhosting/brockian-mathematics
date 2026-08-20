/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex (I)
open Matrix

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

theorem ee_add_neg (k : Fin 19) : ee k + ee (-k) = mu k := by
  have h1 : ee k * ee (-k) = 1 := by
    rw [← ee_add, add_neg_cancel, ee_zero]
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 19 with ht
  have hk : ee k = Complex.exp ((t : ℝ) * I) := ee_eq_exp k
  have hnk : ee (-k) = Complex.exp (-((t : ℝ) * I)) := by
    have hne : Complex.exp ((t : ℝ) * I) ≠ 0 := Complex.exp_ne_zero _
    have := h1
    rw [hk] at this
    rw [Complex.exp_neg]
    field_simp
    linear_combination this
  rw [hk, hnk, mu, ← ht, Complex.ofReal_cos, Complex.cos]
  ring_nf

