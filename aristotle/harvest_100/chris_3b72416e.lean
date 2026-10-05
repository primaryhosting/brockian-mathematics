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
def Cage.WF (C : Cage) : Prop :=
  (∀ e ∈ C.E, (C.ends e).card = 2 ∧ C.ends e ⊆ C.V) ∧
  (∀ f ∈ C.F, C.sides f ⊆ C.E ∧ 3 ≤ (C.sides f).card) ∧
  (∀ e ∈ C.E, (C.F.filter fun f => e ∈ C.sides f).card = 2)

/-- The tetrahedron as a cage with explicit incidence data: vertices `0,1,2,3`, edges
`0,…,5` (edge `i` joining the indicated pair) and the four triangular faces. -/
def tetraCage : Cage where
  V := {0, 1, 2, 3}
  E := {0, 1, 2, 3, 4, 5}
  F := {0, 1, 2, 3}
  ends := fun e =>
    match e with
    | 0 => {0, 1}
    | 1 => {0, 2}
    | 2 => {0, 3}
    | 3 => {1, 2}
    | 4 => {1, 3}
    | 5 => {2, 3}
    | _ => ∅
  sides := fun f =>
    match f with
    | 0 => {0, 1, 3}
    | 1 => {0, 2, 4}
    | 2 => {1, 2, 5}
    | 3 => {3, 4, 5}
    | _ => ∅

/-- The tetrahedral cage is well formed: each of its six edges has two endpoints and lies on
exactly two of the four triangular faces. -/
theorem tetraCage_wf : tetraCage.WF := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Subdivide the edge `e` of a cage by a new vertex `v`: the half of `e` at the endpoint `b`
becomes the new edge `enew`, and every face bounded by `e` is now bounded by `e` and `enew`. -/
def Cage.subdivide (C : Cage) (e enew v b : ℕ) : Cage where
  V := insert v C.V
  E := insert enew C.E
  F := C.F
  ends := fun x =>
    if x = enew then {v, b} else if x = e then insert v ((C.ends e).erase b) else C.ends x
  sides := fun f => if e ∈ C.sides f then insert enew (C.sides f) else C.sides f

@[simp] theorem Cage.subdivide_V (C : Cage) (e enew v b : ℕ) :
    (C.subdivide e enew v b).V = insert v C.V := rfl

@[simp] theorem Cage.subdivide_E (C : Cage) (e enew v b : ℕ) :
    (C.subdivide e enew v b).E = insert enew C.E := rfl

@[simp] theorem Cage.subdivide_F (C : Cage) (e enew v b : ℕ) :
    (C.subdivide e enew v b).F = C.F := rfl

theorem Cage.subdivide_ends_new (C : Cage) (e enew v b : ℕ) :
    (C.subdivide e enew v b).ends enew = {v, b} := by
  simp [Cage.subdivide]

theorem Cage.subdivide_ends_old (C : Cage) {e enew : ℕ} (v b : ℕ) (h : e ≠ enew) :
    (C.subdivide e enew v b).ends e = insert v ((C.ends e).erase b) := by
  simp [Cage.subdivide, h]

theorem Cage.subdivide_ends_other (C : Cage) {e enew x : ℕ} (v b : ℕ)
    (h1 : x ≠ enew) (h2 : x ≠ e) : (C.subdivide e enew v b).ends x = C.ends x := by
  simp [Cage.subdivide, h1, h2]

theorem Cage.subdivide_sides (C : Cage) (e enew v b f : ℕ) :
    (C.subdivide e enew v b).sides f =
      if e ∈ C.sides f then insert enew (C.sides f) else C.sides f := rfl

/-- Subdividing an edge preserves well-formedness: the new vertex has two incident edge halves,
each edge still has exactly two endpoints, and every edge still lies on exactly two faces. -/
theorem Cage.wf_subdivide {C : Cage} (hC : C.WF) {e enew v b : ℕ}
    (he : e ∈ C.E) (hb : b ∈ C.ends e) (hv : v ∉ C.V) (hnew : enew ∉ C.E) :
    (C.subdivide e enew v b).WF := by
  obtain ⟨hedge, hface, hincid⟩ := hC
  have hbV : b ∈ C.V := (hedge e he).2 hb
  have hvb : v ≠ b := fun hcon => hv (hcon ▸ hbV)
  have hne : e ≠ enew := fun hcon => hnew (hcon ▸ he)
  have hsides_mem : ∀ f, ∀ x, x ≠ enew →
      (x ∈ (C.subdivide e enew v b).sides f ↔ x ∈ C.sides f) := by
    intro f x hx
    rw [Cage.subdivide_sides]
    split
    · simp [Finset.mem_insert, hx]
    · rfl
  have hsides_new : ∀ f ∈ C.F,
      (enew ∈ (C.subdivide e enew v b).sides f ↔ e ∈ C.sides f) := by
    intro f hf
    have hnotin : enew ∉ C.sides f := fun hcon => hnew ((hface f hf).1 hcon)
    rw [Cage.subdivide_sides]
    split
    · next h => simp [Finset.mem_insert, h]
    · next h => simp [hnotin, h]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Cage.subdivide_E, Finset.mem_insert] at hx
    rw [Cage.subdivide_V]
    by_cases hxnew : x = enew
    · rw [hxnew, Cage.subdivide_ends_new]
      refine ⟨Finset.card_pair hvb, ?_⟩
      intro y hy
      rcases Finset.mem_insert.1 hy with hy' | hy'
      · rw [hy']; exact Finset.mem_insert_self _ _
      · rw [Finset.mem_singleton] at hy'
        exact Finset.mem_insert_of_mem (hy' ▸ hbV)
    · have hxE : x ∈ C.E := by tauto
      by_cases hxe : x = e
      · rw [hxe, C.subdivide_ends_old v b hne]
        have hsub : (C.ends e).erase b ⊆ C.V :=
          fun y hy => (hedge e he).2 (Finset.erase_subset _ _ hy)
        have hvnot : v ∉ (C.ends e).erase b := fun hcon => hv (hsub hcon)
        refine ⟨?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hvnot, Finset.card_erase_of_mem hb, (hedge e he).1]
        · intro y hy
          rcases Finset.mem_insert.1 hy with hy' | hy'
          · rw [hy']; exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hsub hy')
      · rw [C.subdivide_ends_other v b hxnew hxe]
        exact ⟨(hedge x hxE).1, fun y hy => Finset.mem_insert_of_mem ((hedge x hxE).2 hy)⟩
  · intro f hf
    rw [Cage.subdivide_F] at hf
    have hsub : C.sides f ⊆ C.E := (hface f hf).1
    have hcard : 3 ≤ (C.sides f).card := (hface f hf).2
    rw [Cage.subdivide_E, Cage.subdivide_sides]
    split
    · refine ⟨?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.1 hx with hx' | hx'
        · rw [hx']; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hsub hx')
      · exact le_trans hcard (Finset.card_le_card (Finset.subset_insert _ _))
    · exact ⟨fun x hx => Finset.mem_insert_of_mem (hsub hx), hcard⟩
  · intro x hx
    rw [Cage.subdivide_E, Finset.mem_insert] at hx
    rw [Cage.subdivide_F]
    by_cases hxnew : x = enew
    · have hfil : (C.F.filter fun f => x ∈ (C.subdivide e enew v b).sides f)
          = C.F.filter fun f => e ∈ C.sides f :=
        Finset.filter_congr fun f hf => by
          simpa [hxnew] using hsides_new f hf
      rw [hfil]
      exact hincid e he
    · have hxE : x ∈ C.E := by tauto
      have hfil : (C.F.filter fun f => x ∈ (C.subdivide e enew v b).sides f)
          = C.F.filter fun f => x ∈ C.sides f :=
        Finset.filter_congr fun f _ => by
          simpa using hsides_mem f x hxnew
      rw [hfil]
      exact hincid x hxE

/-- Split the face `f` of a cage by a new diagonal edge `enew` with endpoints `a` and `b`: the
boundary edges of `f` are divided into the part `A`, which stays with `f`, and the rest, which
together with the diagonal bounds the new face `fnew`. -/
def Cage.splitFace (C : Cage) (f fnew enew a b : ℕ) (A : Finset ℕ) : Cage where
  V := C.V
  E := insert enew C.E
  F := insert fnew C.F
  ends := fun x => if x = enew then {a, b} else C.ends x
  sides := fun g =>
    if g = fnew then insert enew (C.sides f \ A)
    else if g = f then insert enew A
    else C.sides g

@[simp] theorem Cage.splitFace_V (C : Cage) (f fnew enew a b : ℕ) (A : Finset ℕ) :
    (C.splitFace f fnew enew a b A).V = C.V := rfl

@[simp] theorem Cage.splitFace_E (C : Cage) (f fnew enew a b : ℕ) (A : Finset ℕ) :
    (C.splitFace f fnew enew a b A).E = insert enew C.E := rfl

@[simp] theorem Cage.splitFace_F (C : Cage) (f fnew enew a b : ℕ) (A : Finset ℕ) :
    (C.splitFace f fnew enew a b A).F = insert fnew C.F := rfl

theorem Cage.splitFace_sides (C : Cage) (f fnew enew a b g : ℕ) (A : Finset ℕ) :
    (C.splitFace f fnew enew a b A).sides g =
      if g = fnew then insert enew (C.sides f \ A)
      else if g = f then insert enew A else C.sides g := rfl

theorem Cage.splitFace_ends (C : Cage) (f fnew enew a b x : ℕ) (A : Finset ℕ) :
    (C.splitFace f fnew enew a b A).ends x = if x = enew then {a, b} else C.ends x := rfl

/-- Splitting a face by a diagonal preserves well-formedness: the diagonal has two endpoints
and lies on exactly the two faces it separates, while every old edge keeps lying on exactly two
faces (one of the two pieces of `f` replacing `f` where necessary). -/
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
theorem ConstructibleCage.wf {C : Cage} (h : ConstructibleCage C) : C.WF := by
  induction h with
  | tetra => exact tetraCage_wf
  | subdivide e enew v b he hb hv hnew _ ih => exact Cage.wf_subdivide ih he hb hv hnew
  | splitFace f fnew enew a b A hf hfnew hnew ha hb hab hA hAcard hBcard _ ih =>
      exact Cage.wf_splitFace ih hf hfnew hnew ha hb hab hA hAcard hBcard

/-- The counts of a constructible cage form a polyhedron in the sense of `Chem.IsPolyhedron`. -/
theorem ConstructibleCage.isPolyhedron {C : Cage} (h : ConstructibleCage C) :
    IsPolyhedron C.V.card C.E.card C.F.card := by
  induction h with
  | tetra =>
      have hV : tetraCage.V.card = 4 := by decide
      have hE : tetraCage.E.card = 6 := by decide
      have hF : tetraCage.F.card = 4 := by decide
      rw [hV, hE, hF]
      exact IsPolyhedron.tetrahedron
  | @subdivide C e enew v b he hb hv hnew _ ih =>
      have hV : (C.subdivide e enew v b).V.card = C.V.card + 1 := by
        rw [Cage.subdivide_V, Finset.card_insert_of_notMem hv]
      have hE : (C.subdivide e enew v b).E.card = C.E.card + 1 := by
        rw [Cage.subdivide_E, Finset.card_insert_of_notMem hnew]
      have hF : (C.subdivide e enew v b).F.card = C.F.card := by rw [Cage.subdivide_F]
      rw [hV, hE, hF]
      exact IsPolyhedron.subdivideEdge ih
  | @splitFace C f fnew enew a b A hf hfnew hnew ha hb hab hA hAcard hBcard _ ih =>
      have hV : (C.splitFace f fnew enew a b A).V.card = C.V.card := by rw [Cage.splitFace_V]
      have hE : (C.splitFace f fnew enew a b A).E.card = C.E.card + 1 := by
        rw [Cage.splitFace_E, Finset.card_insert_of_notMem hnew]
      have hF : (C.splitFace f fnew enew a b A).F.card = C.F.card + 1 := by
        rw [Cage.splitFace_F, Finset.card_insert_of_notMem hfnew]
      rw [hV, hE, hF]
      exact IsPolyhedron.splitFace ih

/-- **Euler's polyhedron formula for cages with full incidence data.**  Every closed surface
built from the tetrahedron by subdividing edges and splitting faces satisfies
`|V| - |E| + |F| = 2`. -/
theorem euler_cage {C : Cage} (h : ConstructibleCage C) :
    (C.V.card : ℤ) - (C.E.card : ℤ) + (C.F.card : ℤ) = 2 :=
  euler_polyhedron h.isPolyhedron

/-- Euler's formula for the tetrahedral cage itself: `4 - 6 + 4 = 2`. -/
theorem euler_tetraCage :
    (tetraCage.V.card : ℤ) - (tetraCage.E.card : ℤ) + (tetraCage.F.card : ℤ) = 2 :=
  euler_cage ConstructibleCage.tetra

end Chem

import Mathlib
import RequestProject.ChemIncidence

/-!
# The buckminsterfullerene cage C₆₀ with explicit incidence data

The truncated icosahedron — the carbon skeleton of buckminsterfullerene C₆₀ — is written down
here as a concrete `Chem.Cage`: 60 carbon atoms (vertices `0,…,59`), 90 bonds (edges
`0,…,89`) and 32 rings (faces `0,…,31`), with the endpoints of every bond and the bonds
bounding every ring given explicitly.  The vertices are the 60 "darts" of the icosahedron
(a vertex together with an incident edge), the rings are the 12 pentagons obtained by cutting
off the icosahedron's vertices and the 20 hexagons coming from its triangles.

All the chemically relevant facts about this structure are then checked by decision procedure:
it is a well-formed closed surface (every bond lies on exactly two rings), every atom has
exactly three bonds, there are exactly 12 pentagonal and 20 hexagonal rings, and Euler's
formula `60 - 90 + 32 = 2` holds.
-/

namespace Chem

set_option maxRecDepth 100000

/-- The carbon skeleton of C₆₀ (the truncated icosahedron) as a cage with explicit incidence
data: 60 vertices, 90 edges, 32 faces. -/
def buckyballCage : Cage where
  V := Finset.range 60
  E := Finset.range 90
  F := Finset.range 32
  ends := fun e =>
    match e with
    | 0 => {0, 1}
    | 1 => {0, 4}
    | 2 => {1, 3}
    | 3 => {2, 3}
    | 4 => {2, 4}
    | 5 => {5, 6}
    | 6 => {5, 8}
    | 7 => {6, 9}
    | 8 => {7, 8}
    | 9 => {7, 9}
    | 10 => {10, 11}
    | 11 => {10, 13}
    | 12 => {11, 14}
    | 13 => {12, 13}
    | 14 => {12, 14}
    | 15 => {15, 16}
    | 16 => {15, 17}
    | 17 => {16, 19}
    | 18 => {17, 18}
    | 19 => {18, 19}
    | 20 => {20, 21}
    | 21 => {20, 22}
    | 22 => {21, 24}
    | 23 => {22, 23}
    | 24 => {23, 24}
    | 25 => {25, 26}
    | 26 => {25, 27}
    | 27 => {26, 28}
    | 28 => {27, 29}
    | 29 => {28, 29}
    | 30 => {30, 31}
    | 31 => {30, 33}
    | 32 => {31, 32}
    | 33 => {32, 34}
    | 34 => {33, 34}
    | 35 => {35, 36}
    | 36 => {35, 38}
    | 37 => {36, 37}
    | 38 => {37, 39}
    | 39 => {38, 39}
    | 40 => {40, 41}
    | 41 => {40, 42}
    | 42 => {41, 43}
    | 43 => {42, 44}
    | 44 => {43, 44}
    | 45 => {45, 47}
    | 46 => {45, 49}
    | 47 => {46, 47}
    | 48 => {46, 48}
    | 49 => {48, 49}
    | 50 => {50, 52}
    | 51 => {50, 53}
    | 52 => {51, 52}
    | 53 => {51, 54}
    | 54 => {53, 54}
    | 55 => {55, 57}
    | 56 => {55, 58}
    | 57 => {56, 57}
    | 58 => {56, 59}
    | 59 => {58, 59}
    | 60 => {0, 5}
    | 61 => {1, 10}
    | 62 => {2, 25}
    | 63 => {3, 30}
    | 64 => {4, 35}
    | 65 => {6, 11}
    | 66 => {7, 15}
    | 67 => {8, 36}
    | 68 => {9, 40}
    | 69 => {12, 20}
    | 70 => {13, 31}
    | 71 => {14, 41}
    | 72 => {16, 37}
    | 73 => {17, 42}
    | 74 => {18, 45}
    | 75 => {19, 55}
    | 76 => {21, 32}
    | 77 => {22, 43}
    | 78 => {23, 46}
    | 79 => {24, 50}
    | 80 => {26, 33}
    | 81 => {27, 38}
    | 82 => {28, 51}
    | 83 => {29, 56}
    | 84 => {34, 52}
    | 85 => {39, 57}
    | 86 => {44, 47}
    | 87 => {48, 53}
    | 88 => {49, 58}
    | 89 => {54, 59}
    | _ => ∅
  sides := fun f =>
    match f with
    | 0 => {0, 1, 2, 3, 4}
    | 1 => {5, 6, 7, 8, 9}
    | 2 => {10, 11, 12, 13, 14}
    | 3 => {15, 16, 17, 18, 19}
    | 4 => {20, 21, 22, 23, 24}
    | 5 => {25, 26, 27, 28, 29}
    | 6 => {30, 31, 32, 33, 34}
    | 7 => {35, 36, 37, 38, 39}
    | 8 => {40, 41, 42, 43, 44}
    | 9 => {45, 46, 47, 48, 49}
    | 10 => {50, 51, 52, 53, 54}
    | 11 => {55, 56, 57, 58, 59}
    | 12 => {0, 5, 10, 60, 61, 65}
    | 13 => {1, 6, 35, 60, 64, 67}
    | 14 => {2, 11, 30, 61, 63, 70}
    | 15 => {3, 25, 31, 62, 63, 80}
    | 16 => {4, 26, 36, 62, 64, 81}
    | 17 => {7, 12, 40, 65, 68, 71}
    | 18 => {8, 15, 37, 66, 67, 72}
    | 19 => {9, 16, 41, 66, 68, 73}
    | 20 => {13, 20, 32, 69, 70, 76}
    | 21 => {14, 21, 42, 69, 71, 77}
    | 22 => {17, 38, 55, 72, 75, 85}
    | 23 => {18, 43, 45, 73, 74, 86}
    | 24 => {19, 46, 56, 74, 75, 88}
    | 25 => {22, 33, 50, 76, 79, 84}
    | 26 => {23, 44, 47, 77, 78, 86}
    | 27 => {24, 48, 51, 78, 79, 87}
    | 28 => {27, 34, 52, 80, 82, 84}
    | 29 => {28, 39, 57, 81, 83, 85}
    | 30 => {29, 53, 58, 82, 83, 89}
    | 31 => {49, 54, 59, 87, 88, 89}
    | _ => ∅

/-- Euler's formula for the explicit C₆₀ cage: `60 - 90 + 32 = 2`. -/
theorem buckyballCage_euler :
    (buckyballCage.V.card : ℤ) - (buckyballCage.E.card : ℤ)
      + (buckyballCage.F.card : ℤ) = 2 := by
  show ((Finset.range 60).card : ℤ) - ((Finset.range 90).card : ℤ)
      + ((Finset.range 32).card : ℤ) = 2
  simp

/-- Every bond of the C₆₀ cage has exactly two carbon atoms as endpoints, every ring is
bounded by at least three bonds, and **every bond lies on exactly two rings**: the explicit
buckyball data is a well-formed closed surface. -/
theorem buckyballCage_wf : buckyballCage.WF := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The C₆₀ cage is 3-regular: every carbon atom lies on exactly three bonds. -/
theorem buckyballCage_cubic :
    ∀ v ∈ buckyballCage.V,
      (buckyballCage.E.filter fun e => v ∈ buckyballCage.ends e).card = 3 := by
  decide

/-- The C₆₀ cage has exactly 12 pentagonal and 20 hexagonal rings. -/
theorem buckyballCage_rings :
    (buckyballCage.F.filter fun f => (buckyballCage.sides f).card = 5).card = 12 ∧
      (buckyballCage.F.filter fun f => (buckyballCage.sides f).card = 6).card = 20 := by
  refine ⟨?_, ?_⟩ <;> decide

end Chem

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- Combinatorial description of sphere-like polyhedra (closed convex polyhedral surfaces),
recorded through their vertex, edge and face counts.

`IsPolyhedron V E F` means: a polyhedral surface with `V` vertices, `E` edges and `F` faces
can be built from the tetrahedron by the standard construction steps

* subdividing an edge by a new vertex (`V+1, E+1, F`);
* joining two vertices of a face by a new diagonal edge (`V, E+1, F+1`);
* erecting a pyramid over a `k`-gonal face, `k ≥ 3` (`V+1, E+k, F+k-1`);
* truncating a vertex of degree `d`, `d ≥ 3` (`V+d-1, E+d, F+1`).

All of these operations preserve the topological type of the surface (a sphere). -/
inductive IsPolyhedron : Nat → Nat → Nat → Prop
  /-- The tetrahedron: 4 vertices, 6 edges, 4 faces. -/
  | tetrahedron : IsPolyhedron 4 6 4
  /-- Subdivide an edge by inserting a new vertex in its interior. -/
  | subdivideEdge {V E F : Nat} : IsPolyhedron V E F → IsPolyhedron (V + 1) (E + 1) F
  /-- Split a face into two by drawing a diagonal. -/
  | splitFace {V E F : Nat} : IsPolyhedron V E F → IsPolyhedron V (E + 1) (F + 1)
  /-- Erect a pyramid over a `k`-gonal face (`k ≥ 3`). -/
  | pyramid {V E F : Nat} (k : Nat) (hk : 3 ≤ k) :
      IsPolyhedron V E F → IsPolyhedron (V + 1) (E + k) (F + (k - 1))
  /-- Truncate (cut off) a vertex of degree `d` (`d ≥ 3`). -/
  | truncate {V E F : Nat} (d : Nat) (hd : 3 ≤ d) :
      IsPolyhedron V E F → IsPolyhedron (V + (d - 1)) (E + d) (F + 1)

/-- **Euler's polyhedron formula.** For a convex polyhedron (for instance a fullerene cage)
with `V` vertices, `E` edges and `F` faces one has `V - E + F = 2`. -/
theorem euler_polyhedron {V E F : Nat} (h : IsPolyhedron V E F) :
    (V : Int) - (E : Int) + (F : Int) = 2 := by
  induction h with
  | tetrahedron => decide
  | subdivideEdge _ ih => omega
  | splitFace _ ih => omega
  | pyramid k hk _ ih => omega
  | truncate d hd _ ih => omega

/-- Subdividing `n` edges, one after another: `V + n` vertices, `E + n` edges, `F` faces. -/
theorem isPolyhedron_iterate_subdivide (n : Nat) {V E F : Nat} (h : IsPolyhedron V E F) :
    IsPolyhedron (V + n) (E + n) F := by
  induction n with
  | zero => exact h
  | succ n ih => exact IsPolyhedron.subdivideEdge ih

/-- Splitting `n` faces by diagonals, one after another: `V` vertices, `E + n` edges,
`F + n` faces. -/
theorem isPolyhedron_iterate_split (n : Nat) {V E F : Nat} (h : IsPolyhedron V E F) :
    IsPolyhedron V (E + n) (F + n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact IsPolyhedron.splitFace ih

/-- The cube: 8 vertices, 12 edges, 6 faces. -/
theorem isPolyhedron_cube : IsPolyhedron 8 12 6 :=
  isPolyhedron_iterate_split 2 (isPolyhedron_iterate_subdivide 4 IsPolyhedron.tetrahedron)

/-- The octahedron: 6 vertices, 12 edges, 8 faces. -/
theorem isPolyhedron_octahedron : IsPolyhedron 6 12 8 :=
  isPolyhedron_iterate_split 4 (isPolyhedron_iterate_subdivide 2 IsPolyhedron.tetrahedron)

/-- The dodecahedron: 20 vertices, 30 edges, 12 faces.  This is also the smallest fullerene
cage, C₂₀. -/
theorem isPolyhedron_dodecahedron : IsPolyhedron 20 30 12 :=
  isPolyhedron_iterate_split 8 (isPolyhedron_iterate_subdivide 16 IsPolyhedron.tetrahedron)

/-- The icosahedron: 12 vertices, 30 edges, 20 faces. -/
theorem isPolyhedron_icosahedron : IsPolyhedron 12 30 20 :=
  isPolyhedron_iterate_split 16 (isPolyhedron_iterate_subdivide 8 IsPolyhedron.tetrahedron)

/-- The whole fullerene family: for every number `h` of hexagonal rings there is a polyhedron
with the fullerene count table `V = 20 + 2h`, `E = 30 + 3h`, `F = 12 + h` (12 pentagons and
`h` hexagons). -/
theorem isPolyhedron_fullerene (h : Nat) : IsPolyhedron (20 + 2 * h) (30 + 3 * h) (12 + h) := by
  have key : IsPolyhedron (20 + 2 * h) (30 + 2 * h + h) (12 + h) :=
    isPolyhedron_iterate_split h (isPolyhedron_iterate_subdivide (2 * h) isPolyhedron_dodecahedron)
  have harith : 30 + 2 * h + h = 30 + 3 * h := by omega
  rw [harith] at key
  exact key

/-- The buckminsterfullerene cage C₆₀ (the truncated icosahedron), with 60 vertices,
90 edges and 32 faces, arises by the above constructions: eight successive pyramids over
triangles turn the tetrahedron into an icosahedral triangulation (12 vertices, 30 edges,
20 faces), and truncating each of its 12 vertices, all of degree 5, produces C₆₀. -/
theorem fullerene_C60 : IsPolyhedron 60 90 32 := by
  have base : IsPolyhedron 4 6 4 := IsPolyhedron.tetrahedron
  -- eight pyramids over triangular faces: (4,6,4) → (12,30,20)
  have pyr : ∀ V E F : Nat, IsPolyhedron V E F → IsPolyhedron (V + 1) (E + 3) (F + 2) :=
    fun _ _ _ h => IsPolyhedron.pyramid 3 (by omega) h
  have h1 : IsPolyhedron 5 9 6 := pyr _ _ _ base
  have h2 : IsPolyhedron 6 12 8 := pyr _ _ _ h1
  have h3 : IsPolyhedron 7 15 10 := pyr _ _ _ h2
  have h4 : IsPolyhedron 8 18 12 := pyr _ _ _ h3
  have h5 : IsPolyhedron 9 21 14 := pyr _ _ _ h4
  have h6 : IsPolyhedron 10 24 16 := pyr _ _ _ h5
  have h7 : IsPolyhedron 11 27 18 := pyr _ _ _ h6
  have icosa : IsPolyhedron 12 30 20 := pyr _ _ _ h7
  -- twelve truncations of degree-5 vertices: each adds (4,5,1)
  have trunc : ∀ V E F : Nat, IsPolyhedron V E F → IsPolyhedron (V + 4) (E + 5) (F + 1) :=
    fun _ _ _ h => IsPolyhedron.truncate 5 (by omega) h
  have t1 : IsPolyhedron 16 35 21 := trunc _ _ _ icosa
  have t2 : IsPolyhedron 20 40 22 := trunc _ _ _ t1
  have t3 : IsPolyhedron 24 45 23 := trunc _ _ _ t2
  have t4 : IsPolyhedron 28 50 24 := trunc _ _ _ t3
  have t5 : IsPolyhedron 32 55 25 := trunc _ _ _ t4
  have t6 : IsPolyhedron 36 60 26 := trunc _ _ _ t5
  have t7 : IsPolyhedron 40 65 27 := trunc _ _ _ t6
  have t8 : IsPolyhedron 44 70 28 := trunc _ _ _ t7
  have t9 : IsPolyhedron 48 75 29 := trunc _ _ _ t8
  have t10 : IsPolyhedron 52 80 30 := trunc _ _ _ t9
  have t11 : IsPolyhedron 56 85 31 := trunc _ _ _ t10
  exact trunc _ _ _ t11

/-- All five Platonic count tables are realized by polyhedra: tetrahedron `(4,6,4)`, cube
`(8,12,6)`, octahedron `(6,12,8)`, dodecahedron `(20,30,12)` and icosahedron `(12,30,20)`. -/
theorem isPolyhedron_platonic_solids :
    IsPolyhedron 4 6 4 ∧ IsPolyhedron 8 12 6 ∧ IsPolyhedron 6 12 8 ∧
      IsPolyhedron 20 30 12 ∧ IsPolyhedron 12 30 20 :=
  ⟨IsPolyhedron.tetrahedron, isPolyhedron_cube, isPolyhedron_octahedron,
    isPolyhedron_dodecahedron, isPolyhedron_icosahedron⟩

/-- Euler's formula for the fullerene C₆₀: `60 - 90 + 32 = 2`. -/
theorem euler_C60 : (60 : Int) - 90 + 32 = 2 := by
  have h := euler_polyhedron fullerene_C60
  omega

/-- **Twelve-pentagon rule for fullerenes.** A fullerene cage is a 3-regular polyhedron
(`2E = 3V`) whose `F` faces are `p` pentagons and `h` hexagons (`F = p + h`,
`2E = 5p + 6h`). Euler's formula then forces exactly 12 pentagons, whatever the number of
hexagons. -/
theorem fullerene_pentagon_count {V E F p h : Nat}
    (hcubic : 2 * E = 3 * V) (hfaces : F = p + h) (hedges : 2 * E = 5 * p + 6 * h)
    (heuler : (V : Int) - (E : Int) + (F : Int) = 2) : p = 12 := by
  omega

end Chem

import Mathlib
import RequestProject.Chem

/-!
# Polyhedral surfaces as genuine finite sets of vertices, edges and faces

`Chem.IsPolyhedron` records a polyhedral surface through its three counts.  Here the same
constructions are carried out on honest finite sets: a polyhedral surface is given by a finite
set `V` of vertices, a finite set `E` of edges and a finite set `F` of faces (all labelled by
natural numbers), and the construction steps genuinely insert, delete and merge elements of
these sets.  Euler's formula is then obtained from the actual cardinalities `V.card`, `E.card`
and `F.card`.
-/

namespace Chem

open Finset

/-- Polyhedral surfaces described by their actual finite sets of vertices, edges and faces.

`ConstructibleSurface V E F` says that the surface with vertex set `V`, edge set `E` and face
set `F` is obtained from the tetrahedron by the standard construction steps, now performed on
the sets themselves:

* `subdivideEdge`: a fresh vertex `v` and a fresh edge `e` are inserted (the old edge is cut
  into two by `v`);
* `splitFace`: a fresh edge `e` (a diagonal) and the fresh face `f` it cuts off are inserted;
* `pyramid`: a fresh apex `v`, a set `newE` of `k ≥ 3` fresh edges joining it to the `k`
  vertices of a face, and the `k - 1` fresh faces beyond the original one;
* `truncate`: a vertex `v` of degree `d ≥ 3` is deleted and replaced by `d` fresh vertices,
  `d` fresh edges and one fresh face.
-/
inductive ConstructibleSurface : Finset ℕ → Finset ℕ → Finset ℕ → Prop
  /-- The tetrahedron, with four labelled vertices, six labelled edges and four labelled
  faces. -/
  | tetrahedron :
      ConstructibleSurface {0, 1, 2, 3} {0, 1, 2, 3, 4, 5} {0, 1, 2, 3}
  /-- Subdivide an edge: insert a fresh vertex `v` and a fresh edge `e`. -/
  | subdivideEdge {V E F : Finset ℕ} (v e : ℕ) (hv : v ∉ V) (he : e ∉ E) :
      ConstructibleSurface V E F → ConstructibleSurface (insert v V) (insert e E) F
  /-- Split a face by a diagonal: insert a fresh edge `e` and a fresh face `f`. -/
  | splitFace {V E F : Finset ℕ} (e f : ℕ) (he : e ∉ E) (hf : f ∉ F) :
      ConstructibleSurface V E F → ConstructibleSurface V (insert e E) (insert f F)
  /-- Erect a pyramid over a `k`-gonal face (`k = newE.card ≥ 3`): a fresh apex `v`, `k` fresh
  edges and `k - 1` fresh faces. -/
  | pyramid {V E F : Finset ℕ} (v : ℕ) (newE newF : Finset ℕ)
      (hv : v ∉ V) (hE : Disjoint newE E) (hF : Disjoint newF F)
      (hk : 3 ≤ newE.card) (hcard : newF.card + 1 = newE.card) :
      ConstructibleSurface V E F →
        ConstructibleSurface (insert v V) (newE ∪ E) (newF ∪ F)
  /-- Truncate a vertex of degree `d = newE.card ≥ 3`: delete the vertex, insert `d` fresh
  vertices, `d` fresh edges and one fresh face. -/
  | truncate {V E F : Finset ℕ} (v f : ℕ) (newV newE : Finset ℕ)
      (hv : v ∈ V) (hVd : Disjoint newV V) (hE : Disjoint newE E) (hf : f ∉ F)
      (hd : 3 ≤ newE.card) (hcard : newV.card = newE.card) :
      ConstructibleSurface V E F →
        ConstructibleSurface (newV ∪ V.erase v) (newE ∪ E) (insert f F)

/-- A surface built from actual finite sets has counts which form a polyhedron in the sense of
`Chem.IsPolyhedron`; the cardinalities of the three sets change exactly as the numerical
constructions prescribe. -/
theorem isPolyhedron_of_constructibleSurface {V E F : Finset ℕ}
    (h : ConstructibleSurface V E F) : IsPolyhedron V.card E.card F.card := by
  induction h with
  | tetrahedron =>
      have hV : ({0, 1, 2, 3} : Finset ℕ).card = 4 := by decide
      have hE : ({0, 1, 2, 3, 4, 5} : Finset ℕ).card = 6 := by decide
      rw [hV, hE]
      exact IsPolyhedron.tetrahedron
  | @subdivideEdge V E F v e hv he _ ih =>
      rw [Finset.card_insert_of_notMem hv, Finset.card_insert_of_notMem he]
      exact IsPolyhedron.subdivideEdge ih
  | @splitFace V E F e f he hf _ ih =>
      rw [Finset.card_insert_of_notMem he, Finset.card_insert_of_notMem hf]
      exact IsPolyhedron.splitFace ih
  | @pyramid V E F v newE newF hv hE hF hk hcard _ ih =>
      have e1 : (insert v V).card = V.card + 1 := Finset.card_insert_of_notMem hv
      have e2 : (newE ∪ E).card = E.card + newE.card := by
        rw [Finset.card_union_of_disjoint hE]; omega
      have e3 : (newF ∪ F).card = F.card + (newE.card - 1) := by
        rw [Finset.card_union_of_disjoint hF]; omega
      rw [e1, e2, e3]
      exact IsPolyhedron.pyramid newE.card hk ih
  | @truncate V E F v f newV newE hv hVd hE hf hd hcard _ ih =>
      have hVpos : 1 ≤ V.card := Finset.one_le_card.2 ⟨v, hv⟩
      have hVd' : Disjoint newV (V.erase v) :=
        hVd.mono_right (Finset.erase_subset v V)
      have e1 : (newV ∪ V.erase v).card = V.card + (newE.card - 1) := by
        rw [Finset.card_union_of_disjoint hVd', Finset.card_erase_of_mem hv]; omega
      have e2 : (newE ∪ E).card = E.card + newE.card := by
        rw [Finset.card_union_of_disjoint hE]; omega
      have e3 : (insert f F).card = F.card + 1 := Finset.card_insert_of_notMem hf
      rw [e1, e2, e3]
      exact IsPolyhedron.truncate newE.card hd ih

/-- **Euler's polyhedron formula for surfaces given by explicit finite sets.**  If the vertex
set `V`, edge set `E` and face set `F` form a polyhedral surface, then
`|V| - |E| + |F| = 2`. -/
theorem euler_surface {V E F : Finset ℕ} (h : ConstructibleSurface V E F) :
    (V.card : ℤ) - (E.card : ℤ) + (F.card : ℤ) = 2 :=
  euler_polyhedron (isPolyhedron_of_constructibleSurface h)

/-- A concrete non-trivial example: erecting a pyramid over one triangular face of the
tetrahedron (apex `4`, three new edges `6, 7, 8`, two new faces `4, 5`) yields the triangular
bipyramid, with explicit vertex, edge and face sets. -/
theorem constructibleSurface_bipyramid :
    ConstructibleSurface (insert 4 {0, 1, 2, 3}) ({6, 7, 8} ∪ {0, 1, 2, 3, 4, 5})
      ({4, 5} ∪ {0, 1, 2, 3}) :=
  ConstructibleSurface.pyramid 4 {6, 7, 8} {4, 5} (by decide) (by decide) (by decide)
    (by decide) (by decide) ConstructibleSurface.tetrahedron

/-- The bipyramid of `constructibleSurface_bipyramid` has 5 vertices, 9 edges and 6 faces, and
indeed `5 - 9 + 6 = 2`. -/
theorem euler_bipyramid :
    ((insert 4 {0, 1, 2, 3} : Finset ℕ).card : ℤ) - (({6, 7, 8} ∪ {0, 1, 2, 3, 4, 5} :
      Finset ℕ).card : ℤ) + (({4, 5} ∪ {0, 1, 2, 3} : Finset ℕ).card : ℤ) = 2 :=
  euler_surface constructibleSurface_bipyramid

end Chem

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib
import RequestProject.Chem

/-!
# Fullerene cages: consequences of Euler's polyhedron formula

Chemical consequences of `Chem.euler_polyhedron` for closed carbon cages.  A fullerene cage is
a convex polyhedron in which every carbon atom has three neighbours (the polyhedron is
3-regular) and every ring is a pentagon or a hexagon.  Euler's formula pins down the whole
count table of such a cage: there are always exactly 12 pentagons, and with `h` hexagons the
cage has `20 + 2h` atoms, `30 + 3h` bonds and `12 + h` rings.
-/

namespace Chem

/-- Full count table of a fullerene cage with `h` hexagonal rings: 12 pentagons,
`F = 12 + h` faces, `V = 20 + 2h` atoms and `E = 30 + 3h` bonds. -/
theorem fullerene_counts {V E F p h : ℕ}
    (hcubic : 2 * E = 3 * V) (hfaces : F = p + h) (hedges : 2 * E = 5 * p + 6 * h)
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2) :
    p = 12 ∧ F = 12 + h ∧ V = 20 + 2 * h ∧ E = 30 + 3 * h := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The smallest fullerene: with no hexagons at all the cage is the dodecahedron C₂₀, with 20
atoms, 30 bonds and 12 pentagonal rings. -/
theorem fullerene_C20_counts {V E F p : ℕ}
    (hcubic : 2 * E = 3 * V) (hfaces : F = p) (hedges : 2 * E = 5 * p)
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2) :
    V = 20 ∧ E = 30 ∧ F = 12 := by
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Buckminsterfullerene: a fullerene cage with 60 atoms has 12 pentagonal and 20 hexagonal
rings, and 90 bonds. -/
theorem fullerene_C60_rings {E F p h : ℕ}
    (hcubic : 2 * E = 3 * 60) (hfaces : F = p + h) (hedges : 2 * E = 5 * p + 6 * h)
    (heuler : (60 : ℤ) - (E : ℤ) + (F : ℤ) = 2) :
    p = 12 ∧ h = 20 ∧ E = 90 ∧ F = 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- No closed carbon cage can be made of hexagons only: a 3-regular polyhedron all of whose
faces are hexagons does not exist.  (This is why every fullerene needs its twelve pentagons,
and why a flat graphene sheet cannot close up without them.) -/
theorem no_all_hexagonal_cage {V E F : ℕ}
    (hcubic : 2 * E = 3 * V) (hhex : 2 * E = 6 * F)
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2) : False := by
  omega

/-- **Every convex polyhedron has a face with at most five sides.**  If every vertex has degree
at least three (`3 * V ≤ 2 * E`, the handshake bound) and `s f` is the number of sides of the
face `f`, then some face is a triangle, quadrilateral or pentagon.  In particular a carbon cage
cannot avoid small rings. -/
theorem exists_face_le_five {V E : ℕ} {faces : Finset ℕ} {s : ℕ → ℕ}
    (hsum : ∑ f ∈ faces, s f = 2 * E) (hdeg : 3 * V ≤ 2 * E)
    (heuler : (V : ℤ) - (E : ℤ) + (faces.card : ℤ) = 2) :
    ∃ f ∈ faces, s f ≤ 5 := by
  by_contra hcon
  push_neg at hcon
  have hsix : ∀ f ∈ faces, 6 ≤ s f := fun f hf => hcon f hf
  have hbound : 6 * faces.card ≤ 2 * E := by
    calc 6 * faces.card = ∑ _f ∈ faces, 6 := by
          simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ f ∈ faces, s f := Finset.sum_le_sum hsix
      _ = 2 * E := hsum
  omega

/-- Dually, **every convex polyhedron has a vertex of degree at most five**: if every face has
at least three sides (`3 * F ≤ 2 * E`) and `d v` is the degree of the vertex `v`, then some
vertex has degree at most five. -/
theorem exists_vertex_degree_le_five {E F : ℕ} {verts : Finset ℕ} {d : ℕ → ℕ}
    (hsum : ∑ v ∈ verts, d v = 2 * E) (hface : 3 * F ≤ 2 * E)
    (heuler : (verts.card : ℤ) - (E : ℤ) + (F : ℤ) = 2) :
    ∃ v ∈ verts, d v ≤ 5 := by
  by_contra hcon
  push_neg at hcon
  have hsix : ∀ v ∈ verts, 6 ≤ d v := fun v hv => hcon v hv
  have hbound : 6 * verts.card ≤ 2 * E := by
    calc 6 * verts.card = ∑ _v ∈ verts, 6 := by
          simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ v ∈ verts, d v := Finset.sum_le_sum hsix
      _ = 2 * E := hsum
  omega

end Chem

import Mathlib
import RequestProject.Chem

/-!
# Consequences of Euler's polyhedron formula

This file records combinatorial consequences of `Chem.euler_polyhedron`: the count relations
between vertices, edges and faces of a polyhedron whose vertices all have the same degree `d`
and whose faces are all `k`-gons, together with the resulting classification of the five
Platonic solids.
-/

namespace Chem

/-- Key counting identity for a polyhedron all of whose vertices have degree `d` and all of
whose faces are `k`-gons: `E * (2*d + 2*k - d*k) = 2*d*k`. -/
theorem regular_count_identity {V E F d k : ℕ}
    (hdeg : 2 * E = d * V) (hface : 2 * E = k * F)
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2) :
    (E : ℤ) * (2 * d + 2 * k - d * k) = 2 * d * k := by
  have h1 : (d : ℤ) * V = 2 * E := by exact_mod_cast hdeg.symm
  have h2 : (k : ℤ) * F = 2 * E := by exact_mod_cast hface.symm
  have h3 : (V : ℤ) + F = E + 2 := by linarith
  linear_combination ((d : ℤ) * k) * h3 - (k : ℤ) * h1 - (d : ℤ) * h2

/-- For a polyhedron with all vertex degrees equal to `d ≥ 3` and all faces `k`-gons with
`k ≥ 3`, one has `(d - 2) * (k - 2) ≤ 3`; this is the inequality behind the classification of
the Platonic solids. -/
theorem regular_degree_bound {V E F d k : ℕ} (hE : 0 < E)
    (hd : 3 ≤ d) (hk : 3 ≤ k)
    (hdeg : 2 * E = d * V) (hface : 2 * E = k * F)
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2) :
    ((d : ℤ) - 2) * ((k : ℤ) - 2) ≤ 3 := by
  have key := regular_count_identity hdeg hface heuler
  have hE' : (1 : ℤ) ≤ (E : ℤ) := by exact_mod_cast hE
  have hd' : (3 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hk' : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  -- `2*d + 2*k - d*k` must be positive, since `E > 0` and the right-hand side is positive
  have hpos : 0 < 2 * (d : ℤ) + 2 * k - d * k := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  nlinarith

/-- **Classification of the Platonic solids.** A polyhedron in which every vertex has the same
degree `d ≥ 3` and every face is a `k`-gon with `k ≥ 3` must be (combinatorially) one of the
five Platonic solids: tetrahedron `(4,6,4)`, cube `(8,12,6)`, octahedron `(6,12,8)`,
dodecahedron `(20,30,12)` or icosahedron `(12,30,20)`. -/
theorem platonic_classification {V E F d k : ℕ} (hE : 0 < E)
    (hd : 3 ≤ d) (hk : 3 ≤ k)
    (hdeg : 2 * E = d * V) (hface : 2 * E = k * F)
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2) :
    (V, E, F) = (4, 6, 4) ∨ (V, E, F) = (8, 12, 6) ∨ (V, E, F) = (6, 12, 8) ∨
      (V, E, F) = (20, 30, 12) ∨ (V, E, F) = (12, 30, 20) := by
  have hbound := regular_degree_bound hE hd hk hdeg hface heuler
  have hd' : (3 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hk' : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hdle : d ≤ 5 := by
    have : (d : ℤ) ≤ 5 := by nlinarith
    exact_mod_cast this
  have hkle : k ≤ 5 := by
    have : (k : ℤ) ≤ 5 := by nlinarith
    exact_mod_cast this
  have heuler' : V + F = E + 2 := by omega
  simp only [Prod.mk.injEq]
  interval_cases d <;> interval_cases k <;> omega

end Chem

