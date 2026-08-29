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

lemma cycInt_disjoint (k : ℕ) (a : Fin (2 * k + 1)) :
    Disjoint (cycInt k a) (cycInt k (a + (k : Fin (2 * k + 1)))) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [cycInt, Finset.mem_image, Finset.mem_range] at hx hx'
  obtain ⟨t, ht, htx⟩ := hx
  obtain ⟨s, hs, hsx⟩ := hx'
  have hE : ((t : Fin (2 * k + 1))) = ((k : Fin (2 * k + 1))) + ((s : Fin (2 * k + 1))) := by
    refine add_left_cancel (a := a) ?_
    rw [htx, ← hsx, add_assoc]
  rw [← Nat.cast_add] at hE
  have h2 := congrArg Fin.val hE
  rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at h2
  omega

/-- The `j`-th vertex of the odd cycle `C_0, C_k, C_{2k}, …` inside `KG_{2k+1,k}`. -/
