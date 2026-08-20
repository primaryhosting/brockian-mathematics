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

theorem chromaticNumber_kneserGraph_le (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).chromaticNumber ≤ (n - 2 * k + 2 : ℕ) :=
  chromaticNumber_le_iff_colorable.2 (kneserGraph_colorable n k hk hn)

/-! ### The base case `k = 1`: `KG_{n,1}` is the complete graph `K_n` -/

/-- `KG_{n,1}` is the complete graph on the `n` singletons. -/
