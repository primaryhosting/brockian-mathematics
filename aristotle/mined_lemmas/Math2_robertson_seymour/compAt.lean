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

def compAt (l : List Comp) (i : ℕ) : Comp := l.getD i (Comp.path 0)

/-- Vertices of the disjoint union of the components listed in `l`: pairs `(i, x)` with `i`
the index of the component and `x` a position inside it. -/
abbrev ForestVerts (l : List Comp) : Type :=
  {p : ℕ × ℕ // p.1 < l.length ∧ p.2 < (compAt l p.1).size}

/-- `Forest l` is the disjoint union of the components listed in `l`. -/
