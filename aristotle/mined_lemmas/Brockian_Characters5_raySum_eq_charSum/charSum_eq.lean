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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` with values in `ℂ`. -/

lemma charSum_eq (x : ZMod 5) :
    ∑ a : ZMod 5, e (a * x) = if x = 0 then (5 : ℂ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [e]
  · rw [if_neg hx]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h := Equiv.sum_comp (Equiv.mulRight₀ x hx) e
    simpa [Equiv.mulRight₀] using h.trans sum_e_univ

/-- The indicator of the ray through `r`, expressed as a character sum. -/
