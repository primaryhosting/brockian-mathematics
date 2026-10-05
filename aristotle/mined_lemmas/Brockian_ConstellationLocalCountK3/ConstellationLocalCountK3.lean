/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The *local count* `ν_p(H)` of a finite tuple `H` of integers at a modulus `p`:
the number of distinct residue classes modulo `p` occupied by the members of `H`. -/

theorem ConstellationLocalCountK3 (H : Finset ℤ) (hH : H.card = 3) :
    Admissible H ↔ (localCount 2 H < 2 ∧ localCount 3 H < 3) := by
  constructor
  · intro h
    exact ⟨h 2 Nat.prime_two, h 3 Nat.prime_three⟩
  · rintro ⟨h2, h3⟩ p hp
    rcases eq_or_ne p 2 with rfl | hp2
    · exact h2
    rcases eq_or_ne p 3 with rfl | hp3
    · exact h3
    have h5 : 5 ≤ p := five_le_of_prime_ne hp hp2 hp3
    exact localCount_lt_of_card_lt (by omega : H.card < p)

/-- Contrapositive form: a triple fails to be an admissible constellation exactly when it
covers all residues mod `2` or all residues mod `3`. -/
