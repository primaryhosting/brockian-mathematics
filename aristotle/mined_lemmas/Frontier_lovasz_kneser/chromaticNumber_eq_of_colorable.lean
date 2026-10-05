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

lemma chromaticNumber_eq_of_colorable {V : Type*} {G : SimpleGraph V} {m : ℕ}
    (h1 : G.Colorable (m + 1)) (h2 : ¬ G.Colorable m) :
    G.chromaticNumber = ((m + 1 : ℕ) : ℕ∞) := by
  refine le_antisymm (chromaticNumber_le_iff_colorable.mpr h1) ?_
  have hlt : ¬ (G.chromaticNumber ≤ ((m : ℕ) : ℕ∞)) := fun h =>
    h2 (chromaticNumber_le_iff_colorable.mp h)
  have := Order.add_one_le_of_lt (lt_of_not_ge hlt)
  exact_mod_cast this

/-- **Lovász–Kneser theorem (base cases).**  The chromatic number of the Kneser graph
`KG_{n,k}` (vertices: the `k`-element subsets of an `n`-element set; edges: pairs of disjoint
subsets) is `n - 2k + 2`.

The upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` is proved in full generality in
`Frontier.kneserGraph_colorable`.  The matching lower bound, which in general requires the
Borsuk–Ulam theorem, is established here in the base cases

* `k = 1`, where `KG_{n,1}` is the complete graph `K_n` and `χ = n`;
* `n = 2k`, where `KG_{2k,k}` is a perfect matching and `χ = 2`;
* `n = 2k + 1`, where `KG_{2k+1,k}` is the odd graph `O_{k+1}` and `χ = 3`, the lower bound
  coming from the odd cycle of cyclically consecutive blocks.

The hypothesis `2 * k ≤ n` is part of the classical statement of the theorem. -/
