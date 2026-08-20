/-
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `a ↦ ω ^ a.val` on `ZMod 5`. -/

lemma omega_ne_one : ω ≠ 1 := by
  rw [ω, Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  field_simp at hn
  have h5 : (1 : ℂ) = 5 * n := by linear_combination hn
  have hz : (1 : ℤ) = 5 * n := by exact_mod_cast h5
  omega

