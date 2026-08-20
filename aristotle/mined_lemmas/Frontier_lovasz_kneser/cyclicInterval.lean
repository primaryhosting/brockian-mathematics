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

def cyclicInterval (k i : ℕ) : Finset (Fin (2 * k + 1)) :=
  (Finset.range k).image
    (fun j => (⟨(i + j) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (2 * k + 1)))

