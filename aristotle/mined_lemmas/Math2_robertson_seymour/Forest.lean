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

def Forest (l : List Comp) : SimpleGraph (ForestVerts l) where
  Adj u v := u.1.1 = v.1.1 ∧ (compAt l u.1.1).Adj u.1.2 v.1.2
  symm := by
    rintro u v ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    rw [← h1]
    exact Comp.adj_symm _ h2
  loopless := ⟨by rintro u ⟨-, h⟩; exact Comp.adj_irrefl _ u.2.2 h⟩

/-! Sanity checks on the definition of `Forest`: consecutive positions inside a component
are adjacent, non-consecutive positions of a path are not, the two ends of a cycle are
adjacent, and distinct components are not joined. -/

example : (Forest [Comp.path 3]).Adj ⟨(0, 0), by decide⟩ ⟨(0, 1), by decide⟩ :=
  ⟨rfl, Or.inl rfl⟩

example : ¬ (Forest [Comp.path 3]).Adj ⟨(0, 0), by decide⟩ ⟨(0, 2), by decide⟩ := by
  rintro ⟨-, h | h⟩ <;> simp at h

example : (Forest [Comp.cycle 0]).Adj ⟨(0, 0), by decide⟩ ⟨(0, 2), by decide⟩ :=
  ⟨rfl, Or.inr rfl⟩

example : ¬ (Forest [Comp.path 3, Comp.path 3]).Adj ((⟨(0, 0), by decide⟩ :
    ForestVerts [Comp.path 3, Comp.path 3])) ⟨(1, 0), by decide⟩ := by
  rintro ⟨h, -⟩
  simp at h

/-- A graph is a *forest of paths and cycles* if it is isomorphic to a disjoint union of
finite paths and cycles.  (This class consists exactly of the finite graphs of maximum
degree at most two, but that structure theorem is not formalised here.) -/
