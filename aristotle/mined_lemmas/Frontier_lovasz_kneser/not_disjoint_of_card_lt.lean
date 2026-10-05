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

lemma not_disjoint_of_card_lt {n k : ℕ} {s t : Finset (Fin n)} (hs : s.card = k)
    (ht : t.card = k) (u : Finset (Fin n)) (hsu : s ⊆ u) (htu : t ⊆ u)
    (hu : u.card < 2 * k) : ¬ Disjoint s t := by
  intro hd
  have h1 : (s ∪ t).card = 2 * k := by
    rw [Finset.card_union_of_disjoint hd, hs, ht]; ring
  have h2 : (s ∪ t).card ≤ u.card := Finset.card_le_card (Finset.union_subset hsu htu)
  omega

/-- The standard greedy colouring: `KG_{n,k}` is `(n - 2k + 2)`-colourable. -/
