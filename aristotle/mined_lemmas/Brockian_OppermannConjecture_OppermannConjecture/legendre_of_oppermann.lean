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


theorem legendre_of_oppermann (H : OppermannConjecture) : LegendreConjecture := by
  intro n hn
  by_cases h1 : n = 1
  · subst h1
    exact ⟨3, (isPrimeB_iff 3).mp (by decide), by omega, by omega⟩
  · obtain ⟨-, p, hp, hp1, hp2⟩ := H n (by omega)
    exact ⟨p, hp, hp1,
      Nat.lt_of_lt_of_le hp2 (Nat.mul_le_mul_right _ (Nat.le_succ n))⟩

/-- Oppermann's conjecture implies the strong Bertrand-type statement that there is a prime
strictly between `n²` and `n² + n`. -/
