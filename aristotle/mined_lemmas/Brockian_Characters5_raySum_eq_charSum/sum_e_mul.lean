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

set_option grind.warning false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character `e` of `ZMod 5`, `e x = ω ^ x.val`. -/

lemma sum_e_mul (t : ZMod 5) :
    ∑ a : ZMod 5, e (a * t) = if t = 0 then (5 : ℂ) else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases ht : t = 0
  · subst ht
    simp [e]
  · rw [if_neg ht]
    have h : ∑ a : ZMod 5, e (a * t) = ∑ b : ZMod 5, e b :=
      Fintype.sum_equiv (Equiv.mulRight₀ t ht) _ _ fun _ => rfl
    rw [h, sum_e_univ]

/-- The indicator of the ray `r` written as a character sum. -/
