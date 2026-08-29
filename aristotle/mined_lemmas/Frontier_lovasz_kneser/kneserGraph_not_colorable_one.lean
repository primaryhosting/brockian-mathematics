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

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of an
`n`-element set. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/

lemma kneserGraph_not_colorable_one (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ¬ (kneserGraph n k).Colorable 1 := by
  intro h
  obtain ⟨s, t, hst⟩ := kneserGraph_exists_adj n k hk hn
  obtain ⟨C⟩ := h
  exact C.valid hst (Subsingleton.elim _ _)

/-! ### The base case `n = 2 * k + 1`: an odd cycle of consecutive blocks -/

/-- The block of `k` cyclically consecutive elements of `Fin (2 * k + 1)` starting at `i`. -/
