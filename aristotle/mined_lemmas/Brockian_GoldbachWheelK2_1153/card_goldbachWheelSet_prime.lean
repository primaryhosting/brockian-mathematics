import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Brockian

/-- The new wheel modulus: the prime `1153`. -/
abbrev wheelModulus : ℕ := 1153


theorem card_goldbachWheelSet_prime (p : ℕ) [Fact (Nat.Prime p)] (n : ZMod p) :
    (goldbachWheelSet p n).card = if n = 0 then p - 1 else p - 2 := by
  have hp : Fintype.card (ZMod p) = p := ZMod.card p
  rw [goldbachWheelSet_prime, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, hp]
  by_cases h : n = 0
  · subst h
    simp
  · rw [Finset.card_insert_of_notMem (by simpa [eq_comm] using h), Finset.card_singleton,
      if_neg h]

/-- **The `K = 2` Goldbach wheel at the new wheel modulus `1153`.**
Exactly `1151` of the `1153` residue classes modulo `1153` are admissible for a Goldbach
splitting `n = a + b`, except in the single case `1153 ∣ n`, where `1152` classes are
admissible. -/
