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

lemma kneser_vertex_nonempty {n k : ℕ} (hk : 1 ≤ k) (A : KneserVertex n k) : A.1.Nonempty := by
  rw [← Finset.card_pos, A.2]; omega

/-! ## The upper bound: `χ(KG_{n,k}) ≤ n - 2k + 2` -/

/-- The standard explicit colouring: colour a `k`-set `A` by `min (min A) (n - 2k + 1)`. -/
