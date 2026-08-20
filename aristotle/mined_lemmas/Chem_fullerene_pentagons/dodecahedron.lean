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

namespace Chem

open Finset

/-- Combinatorial data attached to a polyhedron (equivalently, to a connected
planar graph embedded in the sphere):

* a finite type of vertices and a finite type of faces, and a number `E` of edges;
* `degree v` is the number of edges meeting the vertex `v`;
* `sides f` is the number of edges on the boundary of the face `f`;
* `vertex_handshake` : each edge has two endpoints, so the degrees sum to `2 * E`;
* `face_handshake` : each edge borders two faces, so the side counts sum to `2 * E`;
* `euler` : Euler's polyhedron formula `V - E + F = 2`, written additively to
  avoid truncated subtraction on `ℕ`. -/
structure Polyhedron where
  Vertex : Type
  Face : Type
  [instVertex : Fintype Vertex]
  [instFace : Fintype Face]
  E : ℕ
  degree : Vertex → ℕ
  sides : Face → ℕ
  vertex_handshake : ∑ v : Vertex, degree v = 2 * E
  face_handshake : ∑ f : Face, sides f = 2 * E
  euler : Fintype.card Vertex + Fintype.card Face = E + 2

attribute [instance] Polyhedron.instVertex Polyhedron.instFace

/-- **Every trivalent polyhedron whose faces are all pentagons or hexagons has
exactly 12 pentagonal faces** (the combinatorial heart of the fact that every
fullerene has 12 pentagonal rings).  Note that no bound on the number of
hexagons is needed, and none can be given: hexagons may occur in any number
(other than one). -/

def dodecahedron : Polyhedron where
  Vertex := Fin 20
  Face := Fin 12
  E := 30
  degree := fun _ => 3
  sides := fun _ => 5
  vertex_handshake := by simp
  face_handshake := by simp
  euler := by simp

example : (Finset.univ.filter fun f : dodecahedron.Face => dodecahedron.sides f = 5).card = 12 :=
  fullerene_pentagons dodecahedron (fun _ => rfl) (fun _ => Or.inl rfl)

/-- The truncated icosahedron (the C₆₀ buckyball): 60 trivalent vertices, 90 edges,
12 pentagonal and 20 hexagonal faces. -/
