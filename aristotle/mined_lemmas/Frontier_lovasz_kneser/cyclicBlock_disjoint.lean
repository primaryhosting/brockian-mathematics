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

lemma cyclicBlock_disjoint (k j : ℕ) :
    Disjoint (cyclicBlock k j) (cyclicBlock k (j + k)) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  rw [mem_cyclicBlock] at hx hx'
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hxb⟩ := hx'
  have h : (j + a) % (2 * k + 1) = (j + (k + b)) % (2 * k + 1) := by
    rw [← hxa, hxb]; ring_nf
  have := mod_add_cancel (N := 2 * k + 1) (x := j) (by omega) (by omega) h
  omega

/-- The vertex of `KG_{2k+1,k}` given by the cyclic interval starting at `j`. -/
