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

theorem kneser_chromaticNumber_of_n_eq_two_mul_k_add_one (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).chromaticNumber = (2 * k + 1 - 2 * k + 2 : ℕ) := by
  have h3 : 2 * k + 1 - 2 * k + 2 = 3 := by omega
  rw [h3]
  have hupper : (kneserGraph (2 * k + 1) k).chromaticNumber ≤ ((3 : ℕ) : ℕ∞) := by
    have := (kneser_colorable (2 * k + 1) k hk (by omega)).chromaticNumber_le
    rwa [h3] at this
  have hlower : ((3 : ℕ) : ℕ∞) ≤ (kneserGraph (2 * k + 1) k).chromaticNumber := by
    by_contra hcon
    have hlt : (kneserGraph (2 * k + 1) k).chromaticNumber < ((3 : ℕ) : ℕ∞) := not_le.1 hcon
    have hle : (kneserGraph (2 * k + 1) k).chromaticNumber ≤ ((2 : ℕ) : ℕ∞) := by
      have : ((3 : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) + 1 := by norm_num
      rw [this] at hlt
      exact Order.le_of_lt_add_one hlt
    exact kneser_not_colorable_two k hk (SimpleGraph.chromaticNumber_le_iff_colorable.1 hle)
  exact le_antisymm hupper hlower

/-- **Lovász–Kneser theorem (base cases).**

Lovász's theorem states that the chromatic number of the Kneser graph `KG_{n,k}`
(vertices: the `k`-subsets of an `n`-set; edges: pairs of disjoint `k`-subsets) equals
`n - 2k + 2` whenever `n ≥ 2k ≥ 2`; the lower bound is the deep direction, proved via the
Borsuk–Ulam theorem.

Here we prove the statement in its base cases `k = 1` (where `KG_{n,1}` is the complete
graph `K_n`), `n = 2k` (where `KG_{2k,k}` is a perfect matching) and `n = 2k + 1` (the odd
Kneser graphs, which contain an odd cycle and hence need `3` colors).  The easy upper bound
`χ(KG_{n,k}) ≤ n - 2k + 2` is proved in full generality in `Frontier.kneser_colorable`. -/
