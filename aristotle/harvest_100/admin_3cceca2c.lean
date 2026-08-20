import Mathlib

/-!
# Zeckendorf Small
Category: Fibonacci
Target: Fibonacci.zeckendorf_small
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

namespace Fibonacci

/-- Key intermediate lemma: the values of the three Fibonacci numbers involved. -/
lemma fib_values : Nat.fib 11 = 89 ∧ Nat.fib 6 = 8 ∧ Nat.fib 4 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Zeckendorf representation of `100`: `100 = fib 11 + fib 6 + fib 4`,
with indices `11, 6, 4` pairwise differing by at least `2`. -/
theorem zeckendorf_small : 100 = Nat.fib 11 + Nat.fib 6 + Nat.fib 4 := by
  obtain ⟨h11, h6, h4⟩ := fib_values
  rw [h11, h6, h4]

end Fibonacci

