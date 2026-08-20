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

theorem localCount_le_modulus (H : Finset ℤ) {p : ℕ} (hp : 0 < p) :
    localCount H p ≤ p := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have := Finset.card_le_univ (H.image (fun a : ℤ => (a : ZMod p)))
  simpa [localCount, ZMod.card p] using this

/-- A triple of offsets occupies at most three residue classes. -/
