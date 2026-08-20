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

/-!
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GilbreathConjecture

/-! ## Primes -/

/-- `n` is prime: it is at least `2` and has no divisor `d` with `2 ≤ d < n`. -/

theorem isOdlyzko_row_two {p : Nat → Nat} (hp : IsPrimeEnumeration p) :
    IsOdlyzko (gilbreathRow p 2) 7 := by
  have h0 : p 0 = 2 := enum_zero hp
  have h1 : p 1 = 3 := enum_one hp
  have h2 : p 2 = 5 := enum_two hp
  have h3 : p 3 = 7 := enum_three hp
  have h4 : p 4 = 11 := enum_four hp
  have h5 : p 5 = 13 := enum_five hp
  have h6 : p 6 = 17 := enum_six hp
  have h7 : p 7 = 19 := enum_seven hp
  have h8 : p 8 = 23 := enum_eight hp
  have h9 : p 9 = 29 := enum_nine hp
  refine ⟨by simp [gilbreathRow, diffSeq, adist, h0, h1, h2], ?_⟩
  intro i hi hi7
  have hcases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [gilbreathRow, diffSeq, adist, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- Unconditionally: rows `1` through `9` of the Gilbreath triangle of the primes
begin with `1`. -/
