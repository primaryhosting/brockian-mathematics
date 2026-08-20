import Mathlib

/-!
# Fullerene Pentagons
Category: Chemistry
Target: Chem.fullerene_pentagons
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset

/-! ### Combinatorial model of a trivalent polyhedron -/

/--
A **trivalent polyhedron**, combinatorially: finite types of vertices, edges and faces
together with the incidence maps `edgeEnds` (endpoints of an edge) and `faceEdges` (edges
bounding a face), subject to

* `card_edgeEnds`      : every edge has exactly two endpoints;
* `trivalent`          : every vertex lies on exactly three edges;
* `card_faces_of_edge` : every edge lies on exactly two faces;
* `euler`              : Euler's formula `V - E + F = 2`, stated subtraction-free.
-/
structure TrivalentPolyhedron where
  /-- The vertices. -/
  Vert : Type
  /-- The edges. -/
  Edge : Type
  /-- The faces. -/
  Face : Type
  [fintypeVert : Fintype Vert]
  [fintypeEdge : Fintype Edge]
  [fintypeFace : Fintype Face]
  [decEqVert : DecidableEq Vert]
  [decEqEdge : DecidableEq Edge]
  /-- The set of endpoints of an edge. -/
  edgeEnds : Edge → Finset Vert
  /-- The set of edges bounding a face. -/
  faceEdges : Face → Finset Edge
  /-- Every edge has exactly two endpoints. -/
  card_edgeEnds : ∀ e, (edgeEnds e).card = 2
  /-- Every vertex lies on exactly three edges. -/
  trivalent : ∀ v, (univ.filter fun e => v ∈ edgeEnds e).card = 3
  /-- Every edge lies on exactly two faces. -/
  card_faces_of_edge : ∀ e, (univ.filter fun f => e ∈ faceEdges f).card = 2
  /-- Euler's formula `V - E + F = 2`, written without subtraction. -/
  euler : Fintype.card Vert + Fintype.card Face = Fintype.card Edge + 2

attribute [instance] TrivalentPolyhedron.fintypeVert TrivalentPolyhedron.fintypeEdge
  TrivalentPolyhedron.fintypeFace TrivalentPolyhedron.decEqVert TrivalentPolyhedron.decEqEdge

/--
A **fullerene**: a trivalent polyhedron all of whose faces are pentagons or hexagons.
This is the standard combinatorial model of a fullerene molecule, whose carbon atoms are
the vertices and whose bonds are the edges.
-/
structure Fullerene extends TrivalentPolyhedron where
  /-- Every face is bounded by five or by six edges. -/
  pentagon_or_hexagon : ∀ f : Face, (faceEdges f).card = 5 ∨ (faceEdges f).card = 6

/-- Double counting of a relation between two finite types: summing the row sizes and
summing the column sizes give the same total. -/
theorem sum_card_filter_comm {α β : Type*} [Fintype α] [Fintype β] (r : α → β → Prop)
    [DecidableRel r] :
    ∑ a : α, (univ.filter fun b => r a b).card = ∑ b : β, (univ.filter fun a => r a b).card := by
  simp only [card_filter]
  rw [Finset.sum_comm]

namespace TrivalentPolyhedron

variable (T : TrivalentPolyhedron)

/-- **Handshake relation for a trivalent polyhedron**: `3 V = 2 E`, obtained by counting the
vertex–edge incidences in two ways. -/
theorem three_mul_card_vert : 3 * Fintype.card T.Vert = 2 * Fintype.card T.Edge := by
  have key : ∑ _v : T.Vert, 3 = ∑ e : T.Edge, (T.edgeEnds e).card := by
    have h := sum_card_filter_comm (fun (v : T.Vert) (e : T.Edge) => v ∈ T.edgeEnds e)
    calc ∑ _v : T.Vert, 3
        = ∑ v : T.Vert, (univ.filter fun e => v ∈ T.edgeEnds e).card := by
          simp [T.trivalent]
      _ = ∑ e : T.Edge, (univ.filter fun v => v ∈ T.edgeEnds e).card := h
      _ = ∑ e : T.Edge, (T.edgeEnds e).card := by simp
  simpa [T.card_edgeEnds, Finset.sum_const, mul_comm] using key

/-- **Edge–face incidence count**: the total number of face sides equals `2 E`, since every
edge borders exactly two faces. -/
theorem sum_card_faceEdges : ∑ f : T.Face, (T.faceEdges f).card = 2 * Fintype.card T.Edge := by
  have h := sum_card_filter_comm (fun (f : T.Face) (e : T.Edge) => e ∈ T.faceEdges f)
  calc ∑ f : T.Face, (T.faceEdges f).card
      = ∑ f : T.Face, (univ.filter fun e => e ∈ T.faceEdges f).card := by simp
    _ = ∑ e : T.Edge, (univ.filter fun f => e ∈ T.faceEdges f).card := h
    _ = ∑ _e : T.Edge, 2 := by simp [T.card_faces_of_edge]
    _ = 2 * Fintype.card T.Edge := by simp [Finset.sum_const, mul_comm]

/-- Combining Euler's formula with the handshake relation: `3 F = E + 6`. -/
theorem three_mul_card_face : 3 * Fintype.card T.Face = Fintype.card T.Edge + 6 := by
  have h1 := T.euler
  have h2 := T.three_mul_card_vert
  omega

/--
**Combinatorial curvature identity.** For any trivalent polyhedron, the face sizes satisfy
`∑_f (6 - |f|) = 12`. This is the precise sense in which a trivalent polyhedron carries a
total "pentagon deficiency" of exactly twelve, and it is the engine behind the fullerene
pentagon count.
-/
theorem sum_six_sub_card_faceEdges :
    ∑ f : T.Face, (6 - ((T.faceEdges f).card : ℤ)) = 12 := by
  have hsum : ∑ f : T.Face, ((T.faceEdges f).card : ℤ) = 2 * (Fintype.card T.Edge : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) T.sum_card_faceEdges
  have hface : 3 * (Fintype.card T.Face : ℤ) = (Fintype.card T.Edge : ℤ) + 6 := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) T.three_mul_card_face
  rw [Finset.sum_sub_distrib, hsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith

end TrivalentPolyhedron

namespace Fullerene

variable (P : Fullerene)

/-- The pentagonal faces of a fullerene. -/
def pentagons : Finset P.Face := univ.filter fun f => (P.faceEdges f).card = 5

/-- The hexagonal faces of a fullerene. -/
def hexagons : Finset P.Face := univ.filter fun f => (P.faceEdges f).card = 6

/-- The faces split into pentagons and hexagons. -/
theorem card_face_eq : Fintype.card P.Face = P.pentagons.card + P.hexagons.card := by
  classical
  have hdisj : Disjoint P.pentagons P.hexagons := by
    simp only [pentagons, hexagons]
    rw [Finset.disjoint_filter]
    intro f _ h5
    omega
  have hunion : P.pentagons ∪ P.hexagons = (univ : Finset P.Face) := by
    apply Finset.eq_univ_of_forall
    intro f
    rcases P.pentagon_or_hexagon f with h | h
    · exact Finset.mem_union_left _ (by simp [pentagons, h])
    · exact Finset.mem_union_right _ (by simp [hexagons, h])
  have := Finset.card_union_of_disjoint hdisj
  rw [hunion] at this
  simpa [Finset.card_univ] using this

/-- The total number of face sides of a fullerene is `5 p + 6 h`. -/
theorem sum_card_faceEdges_eq :
    ∑ f : P.Face, (P.faceEdges f).card = 5 * P.pentagons.card + 6 * P.hexagons.card := by
  classical
  have hsplit : (univ : Finset P.Face) = P.pentagons ∪ P.hexagons := by
    apply (Finset.eq_univ_of_forall ?_).symm
    intro f
    rcases P.pentagon_or_hexagon f with h | h
    · exact Finset.mem_union_left _ (by simp [pentagons, h])
    · exact Finset.mem_union_right _ (by simp [hexagons, h])
  have hdisj : Disjoint P.pentagons P.hexagons := by
    simp only [pentagons, hexagons]
    rw [Finset.disjoint_filter]
    intro f _ h5
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have h5 : ∑ f ∈ P.pentagons, (P.faceEdges f).card = 5 * P.pentagons.card := by
    rw [Finset.sum_congr rfl (fun f hf => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
    simpa [pentagons] using hf
  have h6 : ∑ f ∈ P.hexagons, (P.faceEdges f).card = 6 * P.hexagons.card := by
    rw [Finset.sum_congr rfl (fun f hf => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
    simpa [hexagons] using hf
  rw [h5, h6]

end Fullerene

/-! ### The arithmetic core -/

/--
The purely arithmetic content of the theorem: from Euler's formula, trivalence, the
splitting of the faces into pentagons and hexagons, and the face–edge incidence count,
the number of pentagons is forced to be `12`.
-/
theorem fullerene_pentagons_arith
    (V E F p h : ℕ)
    (euler : V + F = E + 2)
    (trivalent : 3 * V = 2 * E)
    (faces : F = p + h)
    (incidences : 5 * p + 6 * h = 2 * E) :
    p = 12 := by
  omega

/-! ### The main theorem -/

/--
**Every fullerene has exactly twelve pentagonal faces.**

For a trivalent polyhedron (in the combinatorial sense of `Chem.TrivalentPolyhedron`:
Euler's formula holds, every vertex lies on three edges, every edge has two endpoints and
borders two faces) all of whose faces are pentagons or hexagons, the number of pentagons is
exactly `12` — independently of the number of hexagons.
-/
theorem fullerene_pentagons (P : Fullerene) : P.pentagons.card = 12 :=
  fullerene_pentagons_arith (Fintype.card P.Vert) (Fintype.card P.Edge) (Fintype.card P.Face)
    P.pentagons.card P.hexagons.card P.euler P.toTrivalentPolyhedron.three_mul_card_vert
    P.card_face_eq
    (by rw [← P.sum_card_faceEdges_eq, P.toTrivalentPolyhedron.sum_card_faceEdges])

/-! ### Non-vacuity: the dodecahedron is a fullerene

The hypotheses packaged in `Chem.Fullerene` are satisfiable: the regular dodecahedron (the
smallest fullerene, `C₂₀`) provides an explicit model with `20` vertices, `30` edges and
`12` pentagonal faces. -/

/-- The endpoints of the `30` edges of the dodecahedron, on the vertex set `Fin 20`. -/
def dodecahedronEdgeEnds : Fin 30 → Finset (Fin 20) :=
  ![{0, 8}, {0, 9}, {0, 10}, {1, 9}, {1, 11}, {1, 13}, {2, 10}, {2, 12}, {2, 14}, {3, 12},
    {3, 13}, {3, 17}, {4, 8}, {4, 15}, {4, 16}, {5, 11}, {5, 15}, {5, 19}, {6, 14}, {6, 16},
    {6, 18}, {7, 17}, {7, 18}, {7, 19}, {8, 14}, {9, 15}, {10, 13}, {11, 17}, {12, 18}, {16, 19}]

/-- The edges bounding each of the `12` pentagonal faces of the dodecahedron. -/
def dodecahedronFaceEdges : Fin 12 → Finset (Fin 30) :=
  ![{1, 2, 3, 5, 26}, {0, 2, 6, 8, 24}, {0, 1, 12, 13, 25}, {4, 5, 10, 11, 27},
    {3, 4, 15, 16, 25}, {6, 7, 9, 10, 26}, {7, 8, 18, 20, 28}, {9, 11, 21, 22, 28},
    {13, 14, 16, 17, 29}, {12, 14, 18, 19, 24}, {15, 17, 21, 23, 27}, {19, 20, 22, 23, 29}]

/-- The regular dodecahedron as a fullerene: all incidence conditions are checked by
decision procedure on the explicit combinatorial data. -/
def dodecahedron : Fullerene where
  Vert := Fin 20
  Edge := Fin 30
  Face := Fin 12
  edgeEnds := dodecahedronEdgeEnds
  faceEdges := dodecahedronFaceEdges
  card_edgeEnds := by decide
  trivalent := by decide
  pentagon_or_hexagon := by decide
  card_faces_of_edge := by decide
  euler := by simp

/-- In particular the statement is not vacuous: the dodecahedron has exactly `12` pentagons. -/
theorem dodecahedron_pentagons : dodecahedron.pentagons.card = 12 :=
  fullerene_pentagons dodecahedron

end Chem

