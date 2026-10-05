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

lemma cyclicBlock_card (k j : ℕ) : (cyclicBlock k j).card = k := by
  rw [cyclicBlock, Finset.card_image_of_injective _ ?inj, Finset.card_univ, Fintype.card_fin]
  case inj =>
    intro a b hab
    have h : (j + a.val) % (2 * k + 1) = (j + b.val) % (2 * k + 1) := congrArg Fin.val hab
    exact Fin.ext (mod_add_cancel (N := 2 * k + 1) (by omega) (by omega) h)

