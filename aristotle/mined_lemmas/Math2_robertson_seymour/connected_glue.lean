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

theorem connected_glue (hC : ∀ v, (K.induce (C v)).Connected)
    (hedge : ∀ v v', G.Adj v v' → ∃ u ∈ C v, ∃ u' ∈ C v', K.Adj u u')
    {B : Set V} (hB : (G.induce B).Connected) : (K.induce (glue C B)).Connected := by
  obtain ⟨a⟩ := hB.nonempty
  obtain ⟨u₀⟩ := (hC a.1).nonempty
  haveI : Nonempty ↥(glue C B) := ⟨⟨u₀.1, mem_glue a.2 u₀.2⟩⟩
  refine SimpleGraph.Connected.mk ?_
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  simp only [glue, Set.mem_iUnion, exists_prop] at hx hy
  obtain ⟨v, hv, hxv⟩ := hx
  obtain ⟨v', hv', hyv'⟩ := hy
  exact reachable_glue_of_walk hC hedge ((hB.preconnected ⟨v, hv⟩ ⟨v', hv'⟩).some) hxv hyv'

end Glue

/-- The minor relation is transitive. -/
