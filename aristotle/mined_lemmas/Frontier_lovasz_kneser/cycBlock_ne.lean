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

lemma cycBlock_ne (k i : ℕ) (hk : 1 ≤ k) : cycBlock k (i + k) ≠ cycBlock k i := by
  intro h
  have hd := disjoint_cycBlock k i
  rw [h] at hd
  have hemp := Finset.disjoint_self.mp hd
  have hc := card_cycBlock k i
  rw [hemp, Finset.card_empty] at hc
  omega

/-- The vertex of `KG_{2k+1,k}` given by the cyclic block starting at `i`. -/
