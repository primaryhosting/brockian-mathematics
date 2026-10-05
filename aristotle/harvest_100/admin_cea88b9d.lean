/-
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
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

namespace CS

/-- **Pigeonhole hash.** Any hash function from an `(n+1)`-element set of keys to an
`n`-element set of hash values has a collision: two distinct keys with the same hash. -/
theorem pigeonhole_hash {n : ℕ} (hash : Fin (n + 1) → Fin n) :
    ∃ a b : Fin (n + 1), a ≠ b ∧ hash a = hash b := by
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by
    simp
  obtain ⟨a, b, hab, h⟩ := Fintype.exists_ne_map_eq_of_card_lt hash hcard
  exact ⟨a, b, hab, h⟩

/-- General form of the pigeonhole principle for hash functions: if the key type is finite
and strictly larger than the (finite) type of hash values, the hash has a collision. -/
theorem pigeonhole_hash_of_card_lt {K V : Type*} [Fintype K] [Fintype V]
    (hash : K → V) (hcard : Fintype.card V < Fintype.card K) :
    ∃ a b : K, a ≠ b ∧ hash a = hash b :=
  Fintype.exists_ne_map_eq_of_card_lt hash hcard

end CS

