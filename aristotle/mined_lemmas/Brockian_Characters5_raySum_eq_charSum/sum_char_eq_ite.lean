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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e` of `ZMod 5` with values in `ℂ`, `e x = ω ^ x.val`. -/

lemma sum_char_eq_ite (x : ZMod 5) :
    ∑ a : ZMod 5, e (a * x) = if x = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hx : x = 0
  · subst hx; simp [e]
  · rw [if_neg hx]
    have h := Equiv.sum_comp (Equiv.mulRight₀ x hx) e
    simpa [sum_e_eq_zero] using h

/-- The indicator of the ray `r` at `n`, expressed as a character sum. -/
