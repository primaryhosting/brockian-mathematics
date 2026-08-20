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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5`, `e x = ω ^ x.val`. -/

theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases ha : a = 0
  · subst ha
    simp [e]
  · rw [if_neg ha,
      Fintype.sum_bijective (fun x => a * x) (Equiv.mulLeft₀ a ha).bijective _ e (fun _ => rfl)]
    exact sum_e

end Characters5
end Brockian

