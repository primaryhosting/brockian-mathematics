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

theorem cyclicInterval_congr (k i i' : ℕ) (h : i % (2 * k + 1) = i' % (2 * k + 1)) :
    cyclicInterval k i = cyclicInterval k i' := by
  unfold cyclicInterval
  refine Finset.image_congr ?_
  intro j _
  apply Fin.ext
  simp only
  rw [Nat.add_mod i j, Nat.add_mod i' j, h]

/-- The vertices of the odd closed walk `cyclicInterval k 0, cyclicInterval k k, …` of length
`2k+1` inside `KG_{2k+1,k}`. -/
