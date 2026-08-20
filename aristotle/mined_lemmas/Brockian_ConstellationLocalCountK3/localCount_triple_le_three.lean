/-
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

/-- The *local count* `ν_p(H)` of a finite set of integer offsets `H` at a modulus `p`:
the number of distinct residue classes modulo `p` occupied by the members of `H`. -/

theorem localCount_triple_le_three (a b c : ℤ) (p : ℕ) :
    localCount ({a, b, c} : Finset ℤ) p ≤ 3 := by
  refine le_trans (localCount_le_card _ _) ?_
  calc ({a, b, c} : Finset ℤ).card ≤ ({b, c} : Finset ℤ).card + 1 := Finset.card_insert_le _ _
    _ ≤ (({c} : Finset ℤ).card + 1) + 1 := by
        exact Nat.add_le_add_right (Finset.card_insert_le _ _) 1
    _ = 3 := by simp

/-- For a prime `p ≥ 5`, every triple is automatically locally admissible. -/
