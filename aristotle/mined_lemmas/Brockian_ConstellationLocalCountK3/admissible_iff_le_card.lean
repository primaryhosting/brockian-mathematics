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

theorem admissible_iff_le_card (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → p ≤ H.card → localCount p H < p := by
  constructor
  · intro h p hp _
    exact h p hp
  · intro h p hp
    rcases le_or_gt p H.card with hle | hgt
    · exact h p hp hle
    · exact localCount_lt_of_card_lt hgt

/-- Any prime other than `2` and `3` is at least `5`. -/
