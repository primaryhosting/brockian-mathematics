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

/-- The vertices of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are distinct and disjoint.  (For `k ≥ 1` the
distinctness condition is automatic; it is included only so that the relation is
irreflexive also in the degenerate case `k = 0`.) -/

def cyclicVertex (k j : ℕ) : KneserVertex (2 * k + 1) k :=
  ⟨cyclicBlock k j, cyclicBlock_card k j⟩

