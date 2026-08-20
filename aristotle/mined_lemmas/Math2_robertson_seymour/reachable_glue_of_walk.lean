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

theorem reachable_glue_of_walk (hC : ∀ v, (K.induce (C v)).Connected)
    (hedge : ∀ v v', G.Adj v v' → ∃ u ∈ C v, ∃ u' ∈ C v', K.Adj u u')
    {B : Set V} : ∀ {a b : ↥B} (_ : (G.induce B).Walk a b) {x y : U}
      (hx : x ∈ C a.1) (hy : y ∈ C b.1),
      (K.induce (glue C B)).Reachable ⟨x, mem_glue a.2 hx⟩ ⟨y, mem_glue b.2 hy⟩ := by
  intro a b w
  induction w with
  | @nil a =>
    intro x y hx hy
    exact reachable_induce_mono (Set.subset_biUnion_of_mem a.2) hx hy
      ((hC a.1).preconnected ⟨x, hx⟩ ⟨y, hy⟩)
  | @cons a c b hac _ ih =>
    intro x y hx hy
    obtain ⟨u, hu, u', hu', huu'⟩ := hedge a.1 c.1 hac
    have h1 : (K.induce (glue C B)).Reachable ⟨x, mem_glue a.2 hx⟩ ⟨u, mem_glue a.2 hu⟩ :=
      reachable_induce_mono (Set.subset_biUnion_of_mem a.2) hx hu
        ((hC a.1).preconnected ⟨x, hx⟩ ⟨u, hu⟩)
    have h2 : (K.induce (glue C B)).Adj ⟨u, mem_glue a.2 hu⟩ ⟨u', mem_glue c.2 hu'⟩ := huu'
    exact (h1.trans h2.reachable).trans (ih hu' hy)

/-- Gluing connected branch sets along a connected set of vertices yields a connected set. -/
