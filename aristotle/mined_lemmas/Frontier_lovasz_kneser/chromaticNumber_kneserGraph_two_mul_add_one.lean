/-
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)

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

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
two of them being adjacent when they are disjoint.  (For `k ≥ 1` disjointness already forces
the two vertices to be distinct; the explicit `s ≠ t` only serves to make the relation
irreflexive in the degenerate case `k = 0`.) -/

theorem chromaticNumber_kneserGraph_two_mul_add_one (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).chromaticNumber = 3 := by
  have hup : (kneserGraph (2 * k + 1) k).chromaticNumber ≤ ((2 * k + 1) - 2 * k + 2 : ℕ) :=
    chromaticNumber_kneserGraph_le (2 * k + 1) k hk (by omega)
  have h3 : ((2 * k + 1) - 2 * k + 2 : ℕ) = 3 := by omega
  rw [h3] at hup
  refine le_antisymm hup ?_
  have h2 : ¬ (kneserGraph (2 * k + 1) k).chromaticNumber ≤ 2 := fun h =>
    not_colorable_two_kneserGraph_odd k hk
      (SimpleGraph.chromaticNumber_le_iff_colorable.1 (by exact_mod_cast h))
  exact Order.add_one_le_of_lt (not_le.1 h2)

/-! ### The Lovász–Kneser theorem in the proved base cases -/

/-- **Lovász–Kneser theorem (base cases).**  The chromatic number of the Kneser graph
`KG_{n,k}` equals `n - 2k + 2`.  This is proved here in the base cases `k = 1`
(where `KG_{n,1}` is the complete graph `K_n`), `n = 2k` (where `KG_{2k,k}` is a perfect
matching) and `n = 2k + 1` (the odd graph, which is not bipartite because it carries a closed
walk of odd length `2k+1`).  The general lower bound is Lovász' theorem, whose proof goes
through the Borsuk–Ulam theorem; the general upper bound is proved above in
`chromaticNumber_kneserGraph_le`. -/
