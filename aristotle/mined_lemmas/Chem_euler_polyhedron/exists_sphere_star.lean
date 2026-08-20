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
