import Mathlib
import RequestProject.Chem

/-!
# Polyhedral cages with full incidence data

The previous modules describe a polyhedral surface by its vertex, edge and face sets.  Here the
incidence structure itself is formalized: a `Cage` carries, besides the three finite sets, the
endpoint set of every edge and the boundary-edge set of every face.  Well-formedness (`Cage.WF`)
demands what a closed polyhedral surface must satisfy:

* every edge has exactly two endpoints, both of them vertices;
* every face is bounded by at least three edges of the surface;
* **every edge lies on exactly two faces** — the closed-surface condition.

The two basic construction steps (subdividing an edge, splitting a face by a diagonal) are
defined on the incidence data and are proved to preserve well-formedness, and Euler's formula
`|V| - |E| + |F| = 2` is proved for every cage built in this way.
-/

namespace Chem

open Finset

/-- A polyhedral cage: finite sets of vertices, edges and faces together with the incidence
data (endpoints of each edge, boundary edges of each face). -/
structure Cage where
  /-- The vertex set. -/
  V : Finset ℕ
  /-- The edge set. -/
  E : Finset ℕ
  /-- The face set. -/
  F : Finset ℕ
  /-- The two endpoints of an edge. -/
  ends : ℕ → Finset ℕ
  /-- The boundary edges of a face. -/
  sides : ℕ → Finset ℕ

/-- Well-formedness of a cage: edges have two endpoints among the vertices, faces are bounded
by at least three edges of the cage, and every edge lies on exactly two faces. -/

theorem Cage.wf_splitFace {C : Cage} (hC : C.WF) {f fnew enew a b : ℕ} {A : Finset ℕ}
    (hf : f ∈ C.F) (hfnew : fnew ∉ C.F) (hnew : enew ∉ C.E)
    (ha : a ∈ C.V) (hb : b ∈ C.V) (hab : a ≠ b)
    (hA : A ⊆ C.sides f) (hAcard : 2 ≤ A.card) (hBcard : 2 ≤ (C.sides f \ A).card) :
    (C.splitFace f fnew enew a b A).WF := by
  obtain ⟨hedge, hface, hincid⟩ := hC
  have hffnew : f ≠ fnew := fun hcon => hfnew (hcon ▸ hf)
  have hsubf : C.sides f ⊆ C.E := (hface f hf).1
  have hAE : A ⊆ C.E := fun x hx => hsubf (hA hx)
  have hnotA : enew ∉ A := fun hcon => hnew (hAE hcon)
  have hnotB : enew ∉ C.sides f \ A := fun hcon => hnew (hsubf (Finset.mem_sdiff.1 hcon).1)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Cage.splitFace_E, Finset.mem_insert] at hx
    rw [Cage.splitFace_V, Cage.splitFace_ends]
    by_cases hxnew : x = enew
    · rw [if_pos hxnew]
      refine ⟨Finset.card_pair hab, ?_⟩
      intro y hy
      rcases Finset.mem_insert.1 hy with hy' | hy'
      · rw [hy']; exact ha
      · rw [Finset.mem_singleton] at hy'; rw [hy']; exact hb
    · rw [if_neg hxnew]
      have hxE : x ∈ C.E := by tauto
      exact hedge x hxE
  · intro g hg
    rw [Cage.splitFace_F, Finset.mem_insert] at hg
    rw [Cage.splitFace_E, Cage.splitFace_sides]
    by_cases hgnew : g = fnew
    · rw [if_pos hgnew]
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.1 hx with hx' | hx'
        · rw [hx']; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hsubf (Finset.mem_sdiff.1 hx').1)
      · rw [Finset.card_insert_of_notMem hnotB]; omega
    · rw [if_neg hgnew]
      have hgF : g ∈ C.F := by tauto
      by_cases hgf : g = f
      · rw [if_pos hgf]
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with hx' | hx'
          · rw [hx']; exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hAE hx')
        · rw [Finset.card_insert_of_notMem hnotA]; omega
      · rw [if_neg hgf]
        exact ⟨fun x hx => Finset.mem_insert_of_mem ((hface g hgF).1 hx), (hface g hgF).2⟩
  · intro x hx
    rw [Cage.splitFace_E, Finset.mem_insert] at hx
    rw [Cage.splitFace_F]
    by_cases hxnew : x = enew
    · -- the diagonal lies exactly on the two pieces `f` and `fnew`
      have hfil : ((insert fnew C.F).filter
          fun g => x ∈ (C.splitFace f fnew enew a b A).sides g) = {fnew, f} := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
          Cage.splitFace_sides]
        constructor
        · rintro ⟨hg, hmem⟩
          by_cases hgnew : g = fnew
          · exact Or.inl hgnew
          · rw [if_neg hgnew] at hmem
            by_cases hgf : g = f
            · exact Or.inr hgf
            · rw [if_neg hgf] at hmem
              have hgF : g ∈ C.F := by tauto
              exact absurd (hxnew ▸ hmem) (fun hcon => hnew ((hface g hgF).1 hcon))
        · rintro (hg | hg)
          · exact ⟨Or.inl hg, by rw [hg, if_pos rfl, hxnew]; exact Finset.mem_insert_self _ _⟩
          · refine ⟨Or.inr (hg ▸ hf), ?_⟩
            rw [hg, if_neg hffnew, if_pos rfl, hxnew]
            exact Finset.mem_insert_self _ _
      rw [hfil, Finset.card_pair (Ne.symm hffnew)]
    · have hxE : x ∈ C.E := by tauto
      have hxA : x ∈ (C.splitFace f fnew enew a b A).sides f ↔ x ∈ A := by
        rw [Cage.splitFace_sides, if_neg hffnew, if_pos rfl, Finset.mem_insert]
        constructor
        · rintro (hcon | h); · exact absurd hcon hxnew
          · exact h
        · exact fun h => Or.inr h
      have hxfnew : x ∈ (C.splitFace f fnew enew a b A).sides fnew ↔ x ∈ C.sides f \ A := by
        rw [Cage.splitFace_sides, if_pos rfl, Finset.mem_insert]
        constructor
        · rintro (hcon | h); · exact absurd hcon hxnew
          · exact h
        · exact fun h => Or.inr h
      have hother : ∀ g ∈ C.F, g ≠ f →
          ((x ∈ (C.splitFace f fnew enew a b A).sides g) ↔ x ∈ C.sides g) := by
        intro g hg hgf
        have hgnew : g ≠ fnew := fun hcon => hfnew (hcon ▸ hg)
        rw [Cage.splitFace_sides, if_neg hgnew, if_neg hgf]
      rw [Finset.filter_insert]
      by_cases hxsf : x ∈ C.sides f
      · by_cases hxinA : x ∈ A
        · -- `x` stays with the face `f`
          have hfnew_no : x ∉ (C.splitFace f fnew enew a b A).sides fnew := by
            rw [hxfnew]; simp [hxinA]
          rw [if_neg hfnew_no]
          have : (C.F.filter fun g => x ∈ (C.splitFace f fnew enew a b A).sides g)
              = C.F.filter fun g => x ∈ C.sides g := by
            refine Finset.filter_congr fun g hg => ?_
            by_cases hgf : g = f
            · subst hgf; rw [hxA]; exact ⟨fun _ => hxsf, fun _ => hxinA⟩
            · exact hother g hg hgf
          rw [this]
          exact hincid x hxE
        · -- `x` moves to the new face `fnew`
          have hxB : x ∈ C.sides f \ A := Finset.mem_sdiff.2 ⟨hxsf, hxinA⟩
          have hfnew_yes : x ∈ (C.splitFace f fnew enew a b A).sides fnew := hxfnew.2 hxB
          rw [if_pos hfnew_yes]
          have hEq : (C.F.filter fun g => x ∈ (C.splitFace f fnew enew a b A).sides g)
              = (C.F.filter fun g => x ∈ C.sides g).erase f := by
            ext g
            simp only [Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨hg, hmem⟩
              by_cases hgf : g = f
              · rw [hgf] at hmem; exact absurd (hxA.1 hmem) hxinA
              · exact ⟨hgf, hg, (hother g hg hgf).1 hmem⟩
            · rintro ⟨hgf, hg, hmem⟩
              exact ⟨hg, (hother g hg hgf).2 hmem⟩
          rw [hEq]
          have hfmem : f ∈ C.F.filter fun g => x ∈ C.sides g := Finset.mem_filter.2 ⟨hf, hxsf⟩
          have hnotmem : fnew ∉ (C.F.filter fun g => x ∈ C.sides g).erase f := by
            intro hcon
            exact hfnew (Finset.mem_filter.1 (Finset.mem_of_mem_erase hcon)).1
          rw [Finset.card_insert_of_notMem hnotmem, Finset.card_erase_of_mem hfmem,
            hincid x hxE]
      · -- `x` was not on `f` at all
        have hxinA : x ∉ A := fun hcon => hxsf (hA hcon)
        have hfnew_no : x ∉ (C.splitFace f fnew enew a b A).sides fnew := by
          rw [hxfnew]; simp [hxsf]
        rw [if_neg hfnew_no]
        have : (C.F.filter fun g => x ∈ (C.splitFace f fnew enew a b A).sides g)
            = C.F.filter fun g => x ∈ C.sides g := by
          refine Finset.filter_congr fun g hg => ?_
          by_cases hgf : g = f
          · subst hgf; rw [hxA]
            exact ⟨fun h => absurd h hxinA, fun h => absurd h hxsf⟩
          · exact hother g hg hgf
        rw [this]
        exact hincid x hxE

/-- Cages built from the tetrahedron by subdividing edges and splitting faces by diagonals,
with all the incidence data carried along. -/
inductive ConstructibleCage : Cage → Prop
  /-- The tetrahedral cage. -/
  | tetra : ConstructibleCage tetraCage
  /-- Subdivide an edge by a fresh vertex, creating a fresh edge. -/
  | subdivide {C : Cage} (e enew v b : ℕ) (he : e ∈ C.E) (hb : b ∈ C.ends e)
      (hv : v ∉ C.V) (hnew : enew ∉ C.E) :
      ConstructibleCage C → ConstructibleCage (C.subdivide e enew v b)
  /-- Split a face by a fresh diagonal edge, creating a fresh face. -/
  | splitFace {C : Cage} (f fnew enew a b : ℕ) (A : Finset ℕ)
      (hf : f ∈ C.F) (hfnew : fnew ∉ C.F) (hnew : enew ∉ C.E)
      (ha : a ∈ C.V) (hb : b ∈ C.V) (hab : a ≠ b)
      (hA : A ⊆ C.sides f) (hAcard : 2 ≤ A.card) (hBcard : 2 ≤ (C.sides f \ A).card) :
      ConstructibleCage C → ConstructibleCage (C.splitFace f fnew enew a b A)

/-- Every cage built in this way is a well-formed closed surface: two endpoints per edge, at
least three edges per face, and exactly two faces along every edge. -/
