import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

open SimpleGraph Finset

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {A : Finset (Fin n) // A.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/

lemma cycInt_card (k : ℕ) (a : Fin (2 * k + 1)) : (cycInt k a).card = k := by
  have hinj : Set.InjOn (fun t : ℕ => a + (t : Fin (2 * k + 1))) (Finset.range k) := by
    intro t ht s hs hts
    simp only [Finset.coe_range, Set.mem_Iio] at ht hs
    have h1 : ((t : Fin (2 * k + 1))) = ((s : Fin (2 * k + 1))) := add_left_cancel hts
    have h2 := congrArg Fin.val h1
    rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h2
    exact h2
  rw [cycInt, Finset.card_image_of_injOn hinj, Finset.card_range]

