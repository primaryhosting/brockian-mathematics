/-
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
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

set_option grind.warning false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp [e, ZMod.val_zero]
  · rw [if_neg ha]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hbij : Function.Bijective (fun x : ZMod 5 => a * x) :=
      (Equiv.mulLeft₀ a ha).bijective
    have := Fintype.sum_bijective _ hbij (fun x => e (a * x)) e (fun x => rfl)
    rw [this, sum_e]

end Brockian.Characters5

