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

theorem robertson_seymour {V : ℕ → Type u} (G : ∀ i, SimpleGraph (V i))
    (hG : ∀ i, IsPathCycleForest (G i)) :
    ∃ i j, i < j ∧ IsMinor (G i) (G j) := by
  choose l hl using hG
  have hpwo :
      {L : List Comp | ∀ x ∈ L, x ∈ (Set.univ : Set Comp)}.PartiallyWellOrderedOn
        (List.SublistForall₂ Comp.le) :=
    Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ Comp.le
      comp_partiallyWellOrderedOn
  obtain ⟨i, j, hij, hsub⟩ := hpwo.exists_lt (f := l) (by simp)
  exact ⟨i, j, hij,
    IsMinor.congr (hl i).some (hl j).some.symm (forest_isMinor_of_sublistForall₂ hsub)⟩

/-- **Well-quasi-ordering by minors for linear forests**, a special case of
`Math2.robertson_seymour`. -/
