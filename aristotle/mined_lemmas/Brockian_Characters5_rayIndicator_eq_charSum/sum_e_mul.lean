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

/-- The primitive fifth root of unity `ω = exp(2πi/5)`. -/

lemma sum_e_mul (b : ZMod 5) : ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  have hsum : ∀ f : ZMod 5 → ℂ, ∑ a : ZMod 5, f a = f 0 + f 1 + f 2 + f 3 + f 4 := by
    intro f
    show ∑ a : Fin 5, f a = _
    rw [Fin.sum_univ_five]
  have hcase : ∀ c : ZMod 5, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by decide
  have key := sum_omega_pow
  rcases hcase b with h | h | h | h | h <;> subst h <;> rw [hsum] <;>
    norm_num +decide [e, ZMod.val] <;> linear_combination key

/-- The indicator of the ray `n ≡ r (mod 5)`. -/
