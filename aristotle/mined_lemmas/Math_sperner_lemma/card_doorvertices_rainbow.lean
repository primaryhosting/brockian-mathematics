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

namespace Math

open Finset

/-! ## Sperner's lemma

We formalise the classical combinatorial content of Sperner's lemma.

A *triangulated simplex* is described combinatorially: the vertices of the simplex are
labelled by a type `ι` (for the `n`-simplex, `ι = Fin (n+1)`), and a triangulation consists
of a finite abstract simplicial complex `faces` of *vertices* (of type `V`) together with,
for each vertex `v`, the *carrier* `carrier v ⊆ ι`: the (unique) minimal face of the big
simplex containing `v`.

For a face `t` of the triangulation, its *span* `span t = ⋃ {carrier v | v ∈ t}` is the
smallest face of the big simplex containing `t`.  For `F ⊆ ι`, the cells of the sub-simplex
spanned by `F` are the faces `s` with `span s ⊆ F` and `s.card = F.card`; these are exactly
the top-dimensional simplices of the induced triangulation of that face of the big simplex.

The single geometric input is then the *door axiom*: if `t` is a face lying inside the
sub-simplex `F` and of codimension one there, then `t` is contained in exactly two cells of
`F` when `t` is interior to `F` (i.e. `span t = F`), and in exactly one cell of `F` when `t`
lies in the boundary of `F` (i.e. `span t ⊊ F`).  This is the standard combinatorial
abstraction of "triangulation of a simplex"; see `Math.trivialTriangulation` and
`Math.subdividedSegment` below for instances.

A *Sperner colouring* assigns to each vertex `v` a colour `c v ∈ carrier v`; a cell of `F`
is *rainbow* if it carries all the colours of `F`.  Sperner's lemma says the number of
rainbow cells is odd. -/

/-- A combinatorial triangulation of the simplex with vertex set `ι`, whose vertices are of
type `V`. -/
structure TriangulatedSimplex (ι V : Type*) [DecidableEq ι] [DecidableEq V] where
  /-- The faces of the triangulation. -/
  faces : Finset (Finset V)
  /-- The carrier of a vertex: the minimal face of the big simplex containing it. -/
  carrier : V → Finset ι
  /-- The empty face belongs to the complex. -/
  empty_mem : (∅ : Finset V) ∈ faces
  /-- The set of faces is closed under passing to subsets. -/
  down_closed : ∀ ⦃s : Finset V⦄, s ∈ faces → ∀ ⦃t : Finset V⦄, t ⊆ s → t ∈ faces
  /-- The door axiom: a codimension-one face `t` of the sub-simplex spanned by `F` lies in
  exactly two cells of `F` if it is interior to `F`, and in exactly one cell of `F` if it
  lies on the boundary of `F`. -/
  door : ∀ (F : Finset ι) (t : Finset V), t ∈ faces → t.card + 1 = F.card →
      t.biUnion carrier ⊆ F →
      {s ∈ faces | s.card = F.card ∧ s.biUnion carrier ⊆ F ∧ t ⊆ s}.card
        = if t.biUnion carrier = F then 2 else 1

namespace TriangulatedSimplex

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] (T : TriangulatedSimplex ι V)

/-- The span of a face: the smallest face of the big simplex containing it. -/

lemma card_doorvertices_rainbow {s : Finset V} {c : V → ι} {F : Finset ι} {i₀ : ι}
    (hi₀ : i₀ ∈ F) (hcard : s.card = F.card) (himg : s.image c = F) :
    {v ∈ s | (s.erase v).image c = F.erase i₀}.card = 1 := by
  have hcimg : (s.image c).card = s.card := by rw [himg, hcard]
  have hinj : ∀ u ∈ s, ∀ v ∈ s, c u = c v → u = v := by
    intro u hu v hv huv
    exact Finset.injOn_of_card_image_eq hcimg (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv
  have hset : {v ∈ s | (s.erase v).image c = F.erase i₀} = {v ∈ s | c v = i₀} := by
    apply Finset.filter_congr
    intro v hv
    rw [image_erase_of_injOn hinj hv, himg]
    constructor
    · intro h
      by_contra hne
      have h1 : i₀ ∈ F.erase (c v) := Finset.mem_erase.mpr ⟨fun h' => hne h'.symm, hi₀⟩
      rw [h] at h1
      exact (Finset.mem_erase.mp h1).1 rfl
    · intro h; rw [h]
  rw [hset]
  obtain ⟨v, hvs, hv⟩ : ∃ v ∈ s, c v = i₀ := by
    have : i₀ ∈ s.image c := by rw [himg]; exact hi₀
    simpa using this
  rw [Finset.card_eq_one]
  refine ⟨v, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hws, hw⟩
    exact hinj w hws v hvs (by rw [hw, hv])
  · rintro rfl; exact ⟨hvs, hv⟩

/-- If the cell `s` is not rainbow, it has an even number of doors. -/
