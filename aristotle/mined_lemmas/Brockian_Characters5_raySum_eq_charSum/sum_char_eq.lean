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

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = exp (2 π i / 5)`. -/

lemma sum_char_eq (x : ZMod 5) :
    ∑ a : ZMod 5, e (a * x) = if x = 0 then (5 : ℂ) else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hx : x = 0
  · subst hx
    simp [e_zero]
  · rw [if_neg hx, ← sum_e_eq_zero]
    have hbij : Function.Bijective (fun a : ZMod 5 => a * x) :=
      Finite.injective_iff_bijective.mp (fun _ _ h => mul_right_cancel₀ hx h)
    exact Fintype.sum_bijective (fun a => a * x) hbij _ _ (fun _ => rfl)

/-- The number of elements of `S` lying on the ray `r` modulo `5`. -/
