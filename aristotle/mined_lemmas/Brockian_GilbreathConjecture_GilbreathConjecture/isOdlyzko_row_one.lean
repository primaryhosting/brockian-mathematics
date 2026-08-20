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

theorem isOdlyzko_row_one {p : Nat → Nat} (hp : IsPrimeEnumeration p) :
    IsOdlyzko (gilbreathRow p 1) 2 := by
  have h0 : p 0 = 2 := enum_zero hp
  have h1 : p 1 = 3 := enum_one hp
  have h2 : p 2 = 5 := enum_two hp
  have h3 : p 3 = 7 := enum_three hp
  refine ⟨by simp [gilbreathRow, diffSeq, adist, h0, h1], ?_⟩
  intro i hi hi2
  have : i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl
  · exact Or.inr (by simp [gilbreathRow, diffSeq, adist, h1, h2])
  · exact Or.inr (by simp [gilbreathRow, diffSeq, adist, h2, h3])

/-- Row `2` of the Gilbreath triangle of the primes starts `1, 0, 2, 2, 2, 2, 2, 2, …`. -/
