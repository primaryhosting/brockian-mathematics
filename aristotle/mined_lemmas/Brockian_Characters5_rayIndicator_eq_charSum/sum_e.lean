/-
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` associated to `ω`. -/

theorem sum_e : ∑ a : ZMod 5, e a = 0 := by
  show ∑ a : Fin 5, e a = 0
  rw [Fin.sum_univ_five]
  have : ∀ k : Fin 5, e k = ω ^ (k : ℕ) := fun k => rfl
  simp only [this]
  norm_num
  linear_combination geom_sum_ω

/-- Orthogonality relation for the character `e`. -/
