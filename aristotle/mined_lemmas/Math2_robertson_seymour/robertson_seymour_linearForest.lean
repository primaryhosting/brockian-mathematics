import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE HEADER: Lean 4 requires `import` to be the first command of a file, so the
module docstring above is placed directly after `import Mathlib` (a `/-! ... -/` block
before the import is a parse error).
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Math2

universe u v w

open SimpleGraph

/-! ## The minor relation -/

/-- `IsMinor H G` says that `H` is a minor of `G`: there is a family of pairwise disjoint,
nonempty, connected *branch sets* `B w ⊆ V(G)`, indexed by the vertices `w` of `H`, such
that adjacent vertices of `H` have an edge of `G` between their branch sets. -/

theorem robertson_seymour_linearForest {V : ℕ → Type u} (G : ∀ i, SimpleGraph (V i))
    (hG : ∀ i, IsLinearForest (G i)) :
    ∃ i j, i < j ∧ IsMinor (G i) (G j) :=
  robertson_seymour G fun i => (hG i).isPathCycleForest

/-! ## The general statement

For the record, here is the statement of the full Robertson–Seymour graph minor theorem for
arbitrary finite graphs.  The theorem proved above, `Math2.robertson_seymour`, is its
restriction to the class of disjoint unions of paths and cycles; the general case is not
proved here. -/
