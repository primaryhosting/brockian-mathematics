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

theorem reachable_induce_mono {V : Type u} {G : SimpleGraph V} {S T : Set V} (hST : S ⊆ T)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (h : (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    (G.induce T).Reachable ⟨x, hST hx⟩ ⟨y, hST hy⟩ := by
  let f : G.induce S →g G.induce T := ⟨fun z => ⟨z.1, hST z.2⟩, fun {_ _} hab => hab⟩
  exact h.map f

section Glue

variable {V : Type u} {U : Type v} {G : SimpleGraph V} {K : SimpleGraph U} {C : V → Set U}

/-- The union of the branch sets attached to a set `B` of vertices. -/
