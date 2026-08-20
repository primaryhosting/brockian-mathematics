import Mathlib

/-!
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` given by `x ↦ ω ^ x`. -/

theorem sum_char_eq (t : ZMod 5) : ∑ a : ZMod 5, e (a * t) = if t = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases h : t = 0
  · subst h; simp [e]
  · rw [if_neg h,
      Fintype.sum_equiv (Equiv.mulRight₀ t h) (fun a => e (a * t)) e (fun _ => rfl),
      sum_zmod_five]
    show (1 : ℂ) + ω ^ 1 + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0
    linear_combination geom_sum_omega

/-- The indicator of the ray `r` as a character sum. -/
