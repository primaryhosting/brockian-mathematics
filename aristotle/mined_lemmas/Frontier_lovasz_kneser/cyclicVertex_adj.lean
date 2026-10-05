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

lemma cyclicVertex_adj (k j : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).Adj (cyclicVertex k j) (cyclicVertex k (j + k)) := by
  refine ⟨?_, cyclicBlock_disjoint k j⟩
  intro h
  have h1 : cyclicBlock k j = cyclicBlock k (j + k) := congrArg Subtype.val h
  have hd := cyclicBlock_disjoint k j
  rw [← h1] at hd
  have hne : (cyclicBlock k j).Nonempty := by
    rw [← Finset.card_pos, cyclicBlock_card]; omega
  obtain ⟨x, hx⟩ := hne
  exact (Finset.disjoint_left.mp hd hx) hx

/-- `KG_{2k+1,k}` is not `2`-colorable, because the cyclic intervals form an odd cycle. -/
