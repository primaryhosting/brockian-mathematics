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

theorem oddWalk_adj (k j : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).Adj (oddWalk k j) (oddWalk k (j + 1)) := by
  have hd : Disjoint (cyclicInterval k (j * k)) (cyclicInterval k ((j + 1) * k)) := by
    have h := disjoint_cyclicInterval k (j * k)
    rwa [show (j + 1) * k = j * k + k by ring]
  refine ⟨?_, hd⟩
  intro h
  have h' : cyclicInterval k (j * k) = cyclicInterval k ((j + 1) * k) := congrArg Subtype.val h
  rw [← h'] at hd
  have he := disjoint_self.1 hd
  have hc := card_cyclicInterval k (j * k)
  rw [he] at hc
  simp at hc
  omega

