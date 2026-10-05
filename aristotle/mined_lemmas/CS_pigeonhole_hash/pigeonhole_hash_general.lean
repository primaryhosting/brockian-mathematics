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


namespace CS

/-- **Pigeonhole hash.** Any hash function from an `(n+1)`-element set of keys
into an `n`-element set of buckets has a collision: two distinct keys mapped to
the same bucket. -/

theorem pigeonhole_hash_general {K B : Type*} [Fintype K] [Fintype B]
    (f : K → B) (h : Fintype.card B < Fintype.card K) :
    ∃ a b : K, a ≠ b ∧ f a = f b :=
  Fintype.exists_ne_map_eq_of_card_lt f h

end CS

