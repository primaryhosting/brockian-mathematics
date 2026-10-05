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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace OddZumkeller

/-- A positive natural number `n` is a *Zumkeller number* if its set of divisors can be split
into two parts having the same sum. -/

theorem zumkeller_945 : Odd (945 : ℕ) ∧ Zumkeller 945 ∧ (945 : ℕ).primeFactors.card = 3 := by
  refine ⟨by decide, ⟨by norm_num, {15, 945}, ?_, ?_⟩, ?_⟩
  · rw [divisors_945]; decide
  · rw [divisors_945]; decide
  · have h : (945 : ℕ).primeFactors = {3, 5, 7} := by simp [Nat.primeFactors]
    rw [h]; decide

end OddZumkeller

/-- **The structure statement for odd Zumkeller numbers**: every odd Zumkeller number has at
least three distinct prime factors.  (This is sharp: `945 = 3 ^ 3 * 5 * 7` is an odd Zumkeller
number with exactly three distinct prime factors, see `OddZumkeller.zumkeller_945`.) -/
