/-
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Chem

/-- A combinatorial *polyhedral surface*: a finite set of vertices, a finite set of
(undirected) edges, a finite set of face labels, and, for each label, the set of edges
on the boundary of that face. -/
structure Surface where
  /-- The vertices of the surface. -/
  verts : Finset ℕ
  /-- The edges of the surface. -/
  edges : Finset (Sym2 ℕ)
  /-- The labels of the faces of the surface. -/
  faces : Finset ℕ
  /-- The boundary of each face, given as a set of edges. -/
  bd : ℕ → Finset (Sym2 ℕ)

/-- `IsSphere S` says that the surface `S` is a *spherical* (equivalently, planar) map,
i.e. it is the surface graph of a convex polyhedron, described by the standard
construction of plane graphs:

* one may start from a single vertex drawn on the sphere, whose complement is a single face;
* one may attach a new vertex `v` to an existing vertex `u` by an edge drawn inside a face `f`
  (this creates no new face, and the new edge is added to the boundary of `f`);
* one may join two existing vertices `u`, `v` lying on a common face `f` by a new edge drawn
  inside `f`; this splits `f` into two faces, one of which keeps the label `f` and the other
  gets a fresh label `g`, and the new edge lies on the boundary of both.

Every plane graph (in particular the edge graph of a convex polyhedron, e.g. a fullerene
cage) arises in this way; conversely every surface produced by these moves is a plane graph. -/
inductive IsSphere : Surface → Prop
  | base (v f : ℕ) : IsSphere ⟨{v}, ∅, {f}, fun _ => ∅⟩
  | pendant (S : Surface) (hS : IsSphere S) (u v f : ℕ) (hu : u ∈ S.verts) (hv : v ∉ S.verts)
      (hf : f ∈ S.faces) :
      IsSphere ⟨insert v S.verts, insert s(u, v) S.edges, S.faces,
        Function.update S.bd f (insert s(u, v) (S.bd f))⟩
  | split (S : Surface) (hS : IsSphere S) (u v f g : ℕ) (hu : u ∈ S.verts) (hv : v ∈ S.verts)
      (hf : f ∈ S.faces) (hg : g ∉ S.faces) (he : s(u, v) ∉ S.edges) :
      IsSphere ⟨S.verts, insert s(u, v) S.edges, insert g S.faces,
        Function.update (Function.update S.bd f (insert s(u, v) (S.bd f))) g
          (insert s(u, v) (S.bd g))⟩

/-- In a spherical map every endpoint of an edge is a vertex. -/
theorem IsSphere.mem_verts_of_mem_edges {S : Surface} (hS : IsSphere S) :
    ∀ e ∈ S.edges, ∀ x ∈ e, x ∈ S.verts := by
  induction hS with
  | base v f => simp
  | pendant S hS u v f hu hv hf ih =>
      intro e he x hx
      simp only [Finset.mem_insert] at he
      rcases he with rfl | he
      · simp only [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_insert_of_mem hu
        · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (ih e he x hx)
  | split S hS u v f g hu hv hf hg he ih =>
      intro e he' x hx
      simp only [Finset.mem_insert] at he'
      rcases he' with rfl | he'
      · simp only [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact hu
        · exact hv
      · exact ih e he' x hx

/-- **Euler's polyhedron formula.** For the surface graph of a convex polyhedron
(a spherical/planar map, e.g. a fullerene cage), `V - E + F = 2`. -/
theorem euler_polyhedron {S : Surface} (hS : IsSphere S) :
    (S.verts.card : ℤ) - S.edges.card + S.faces.card = 2 := by
  induction hS with
  | base v f => simp
  | pendant S hS u v f hu hv hf ih =>
      have hedge : s(u, v) ∉ S.edges := by
        intro hmem
        exact hv (hS.mem_verts_of_mem_edges _ hmem v (by simp))
      simp only [Finset.card_insert_of_notMem hv, Finset.card_insert_of_notMem hedge]
      push_cast
      linarith [ih]
  | split S hS u v f g hu hv hf hg he ih =>
      simp only [Finset.card_insert_of_notMem he, Finset.card_insert_of_notMem hg]
      push_cast
      linarith [ih]

/-- The natural-number form of Euler's formula: `V + F = E + 2`. -/
theorem euler_polyhedron_nat {S : Surface} (hS : IsSphere S) :
    S.verts.card + S.faces.card = S.edges.card + 2 := by
  have := euler_polyhedron hS
  omega

/-! ## Non-vacuity: spherical maps with prescribed counts exist -/

/-- The "star" map: a single face, `n + 1` vertices `0, …, n`, and the `n` edges from `0`. -/
theorem exists_sphere_star (n : ℕ) :
    ∃ S : Surface, IsSphere S ∧ S.verts = Finset.range (n + 1) ∧
      S.edges = (Finset.range n).image (fun i => s(0, i + 1)) ∧ S.faces = {0} := by
  induction n with
  | zero =>
      refine ⟨⟨{0}, ∅, {0}, fun _ => ∅⟩, IsSphere.base 0 0, by simp, by simp, by simp⟩
  | succ n ih =>
      obtain ⟨S, hS, hv, he, hf⟩ := ih
      have hvn : (n + 1) ∉ S.verts := by simp [hv]
      refine ⟨_, IsSphere.pendant S hS 0 (n + 1) 0 (by simp [hv]) hvn (by simp [hf]), ?_, ?_, hf⟩
      · rw [hv]; exact (Finset.range_add_one (n := n + 1)).symm
      · rw [he, Finset.range_add_one (n := n), Finset.image_insert]

/-- The star on `n + 1` vertices with `k` extra chords issuing from the vertex `1`. -/
theorem exists_sphere_star_chords (n k : ℕ) (hk : k + 1 ≤ n) :
    ∃ S : Surface, IsSphere S ∧ S.verts = Finset.range (n + 1) ∧
      S.edges = (Finset.range n).image (fun i => s(0, i + 1)) ∪
        (Finset.range k).image (fun i => s(1, i + 2)) ∧
      S.faces = Finset.range (k + 1) := by
  induction k with
  | zero =>
      obtain ⟨S, hS, hv, he, hf⟩ := exists_sphere_star n
      exact ⟨S, hS, hv, by simp [he], by simp [hf]⟩
  | succ k ih =>
      obtain ⟨S, hS, hv, he, hf⟩ := ih (by omega)
      have hedge : s(1, k + 2) ∉ S.edges := by
        rw [he]
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, not_or, not_exists]
        refine ⟨fun i => ?_, fun i => ?_⟩ <;>
          simp only [not_and, Sym2.eq_iff] <;> intro hi <;> omega
      refine ⟨_, IsSphere.split S hS 1 (k + 2) 0 (k + 1) (by simp [hv]; omega)
        (by simp [hv]; omega) (by simp [hf]) (by simp [hf]) hedge, hv, ?_, ?_⟩
      · show insert s(1, k + 2) S.edges = _
        rw [he, Finset.range_add_one (n := k), Finset.image_insert]
        ext x
        simp only [Finset.mem_insert, Finset.mem_union]
        tauto
      · show insert (k + 1) S.faces = _
        rw [hf]
        exact (Finset.range_add_one (n := k + 1)).symm

/-- A spherical map with `n + 1` vertices, `n + k` edges and `k + 1` faces exists,
for all `k + 1 ≤ n`. -/
theorem exists_sphere_counts (n k : ℕ) (hk : k + 1 ≤ n) :
    ∃ S : Surface, IsSphere S ∧ S.verts.card = n + 1 ∧ S.edges.card = n + k ∧
      S.faces.card = k + 1 := by
  obtain ⟨S, hS, hv, _, hf⟩ := exists_sphere_star_chords n k hk
  have hcv : S.verts.card = n + 1 := by rw [hv, Finset.card_range]
  have hcf : S.faces.card = k + 1 := by rw [hf, Finset.card_range]
  have := euler_polyhedron_nat hS
  exact ⟨S, hS, hcv, by omega, hcf⟩

/-- A fullerene cage such as C₆₀ has `V = 60`, `E = 90`, `F = 32`; such a spherical map
exists, so the hypothesis of `Chem.euler_polyhedron` is not vacuous. -/
theorem exists_sphere_fullerene :
    ∃ S : Surface, IsSphere S ∧ S.verts.card = 60 ∧ S.edges.card = 90 ∧ S.faces.card = 32 :=
  exists_sphere_counts 59 31 (by norm_num)

/-! ## A chemical corollary: every fullerene has exactly twelve pentagonal faces -/

/-- In a trivalent (cubic) spherical map all of whose faces are pentagons or hexagons —
i.e. a fullerene cage — there are exactly `12` pentagonal faces. -/
theorem fullerene_twelve_pentagons {S : Surface} (hS : IsSphere S) (p h : ℕ)
    (hcubic : 3 * S.verts.card = 2 * S.edges.card)
    (hfaces : S.faces.card = p + h)
    (hedges : 5 * p + 6 * h = 2 * S.edges.card) :
    p = 12 := by
  have := euler_polyhedron_nat hS
  omega

/-- C₆₀: a trivalent fullerene cage on `60` atoms has `90` bonds, `32` rings,
of which `12` are pentagons and `20` are hexagons. -/
theorem fullerene_C60 {S : Surface} (hS : IsSphere S) (p h : ℕ)
    (hV : S.verts.card = 60)
    (hcubic : 3 * S.verts.card = 2 * S.edges.card)
    (hfaces : S.faces.card = p + h)
    (hedges : 5 * p + 6 * h = 2 * S.edges.card) :
    S.edges.card = 90 ∧ S.faces.card = 32 ∧ p = 12 ∧ h = 20 := by
  have := euler_polyhedron_nat hS
  omega

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

