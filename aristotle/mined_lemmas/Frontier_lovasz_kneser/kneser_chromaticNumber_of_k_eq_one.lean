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

theorem kneser_chromaticNumber_of_k_eq_one (n : ℕ) (h2 : 2 ≤ n) :
    (kneserGraph n 1).chromaticNumber = (n - 2 * 1 + 2 : ℕ) := by
  have hupper : (kneserGraph n 1).chromaticNumber ≤ (n - 2 * 1 + 2 : ℕ) :=
    (kneser_colorable n 1 le_rfl (by omega)).chromaticNumber_le
  have hlower : (n : ℕ∞) ≤ (kneserGraph n 1).chromaticNumber := by
    refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (ι := Fin n) (by simp)
      (fun i => ⟨{i}, by simp⟩) ?_
    intro i j hij
    refine ⟨?_, ?_⟩
    · simp only [ne_eq, Subtype.mk.injEq, Finset.singleton_inj]
      exact hij
    · simpa using hij
  have hn : n - 2 * 1 + 2 = n := by omega
  rw [hn] at hupper ⊢
  exact le_antisymm hupper hlower

/-- For `n = 2k` (with `k ≥ 1`) the Kneser graph is a perfect matching, so its chromatic
number is `2`. -/
