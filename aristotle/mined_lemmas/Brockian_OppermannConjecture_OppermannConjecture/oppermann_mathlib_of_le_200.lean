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


theorem oppermann_mathlib_of_le_200 (n : ℕ) (hn : 1 < n) (hn' : n ≤ 200) :
    (∃ p : ℕ, Nat.Prime p ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ p : ℕ, Nat.Prime p ∧ n * n < p ∧ p < n * (n + 1)) := by
  simpa only [isPrimeNat_iff_prime] using oppermann_of_le_200 n hn hn'

end Brockian.OppermannConjecture

