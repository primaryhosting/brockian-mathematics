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

theorem not_colorable_two_kneserGraph_odd (k : ℕ) (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k + 1) k).Colorable 2 := by
  rintro ⟨C⟩
  have key : ∀ j, (C (oddWalk k j)).val % 2 = ((C (oddWalk k 0)).val + j) % 2 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hne : C (oddWalk k j) ≠ C (oddWalk k (j + 1)) := C.valid (oddWalk_adj k j hk)
      have h1 : (C (oddWalk k j)).val ≠ (C (oddWalk k (j + 1))).val := fun h => hne (Fin.ext h)
      have h2 := (C (oddWalk k j)).isLt
      have h3 := (C (oddWalk k (j + 1))).isLt
      omega
  have h0 := key (2 * k + 1)
  rw [oddWalk_period] at h0
  have h4 := (C (oddWalk k 0)).isLt
  omega

/-- The chromatic number of the odd graph `KG_{2k+1,k}` is `3` (for `k ≥ 1`). -/
