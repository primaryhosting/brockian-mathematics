/-
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`,
and two of them are adjacent when they are disjoint. -/

lemma kneserVertex_nonempty {n k : ℕ} (hk : 1 ≤ k) (s : KneserVertex n k) :
    (s : Finset (Fin n)).Nonempty := by
  rw [← Finset.card_pos, s.2]
  omega

/-- The colouring witnessing `χ(KG_{n,k}) ≤ n - 2k + 2`: a `k`-set `S` gets colour
`min (S.min') (n + 1 - 2k)`. -/
