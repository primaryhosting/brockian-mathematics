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

lemma oddWalk_period (k : ℕ) : oddWalk k (2 * k + 1) = oddWalk k 0 := by
  apply Subtype.ext
  show cycInt k _ = cycInt k _
  congr 1
  apply Fin.val_injective
  rw [Fin.val_natCast, Fin.val_natCast]
  simp [Nat.mul_mod_right]

/-- The odd graph `KG_{2k+1,k}` is not `2`-colourable: it contains a closed walk of odd
length `2k+1`. -/
