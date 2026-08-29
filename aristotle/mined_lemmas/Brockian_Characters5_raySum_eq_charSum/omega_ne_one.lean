/-
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` sending `x` to `ω ^ x`. -/

theorem omega_ne_one : ω ≠ 1 := by
  rw [ω, Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  have h2 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at hn
  have : (1 : ℤ) = 5 * n := by exact_mod_cast hn
  omega

/-- The character sum of `e` over all of `ZMod 5` vanishes. -/
