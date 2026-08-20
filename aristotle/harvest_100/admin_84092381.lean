/-!
# Fullerene Pentagons
Category: Chemistry
Target: Chem.fullerene_pentagons
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: the required header comment must be the very first thing in the file, and Lean
only accepts `import` commands before any other syntax, so this file carries no
imports and is stated with `Nat`.  Nothing beyond Lean core is needed here.
-/

namespace Chem

/-- **Fullerene pentagon count.**

A trivalent convex polyhedron all of whose faces are pentagons or hexagons has
exactly `12` pentagons.

Here `V`, `E`, `F` are the numbers of vertices, edges and faces, `p` the number of
pentagonal faces and `h` the number of hexagonal faces.  The hypotheses are:

* `euler`   : Euler's formula `V - E + F = 2`, written over `Nat` as `V + F = E + 2`;
* `trivalent`: every vertex lies on exactly three edges, so counting vertex–edge
  incidences gives `3 * V = 2 * E`;
* `faces`   : every face is a pentagon or a hexagon, `p + h = F`;
* `edges`   : counting edge–face incidences, each edge lying on two faces,
  `5 * p + 6 * h = 2 * E`.

The conclusion `p = 12` follows by linear arithmetic: multiplying Euler's formula by
`6` and substituting `6 * V = 4 * E`, `6 * F = 6 * p + 6 * h` and
`12 * E = 30 * p + 36 * h` eliminates `V`, `E`, `F` and `h`, leaving `p = 12`.
Note that the number `h` of hexagons is not determined: only the pentagon count is. -/
theorem fullerene_pentagons
    (V E F p h : Nat)
    (euler : V + F = E + 2)
    (trivalent : 3 * V = 2 * E)
    (faces : p + h = F)
    (edges : 5 * p + 6 * h = 2 * E) :
    p = 12 := by
  omega

/-! ### A version stated with an explicit list of face sizes

Instead of postulating the counts `F`, `p`, `h` and the relations between them, we
record the polyhedron's faces as a list `faceSizes` of face sizes, assume each entry
is `5` or `6`, and read off `F = faceSizes.length`, `p = faceSizes.count 5` and
`2 * E = faceSizes.sum` directly. -/

/-- In a list of face sizes all equal to `5` or `6`, the pentagons and hexagons
account for all the faces. -/
theorem count_pentagons_add_count_hexagons
    (faceSizes : List Nat) (pentOrHex : ∀ s ∈ faceSizes, s = 5 ∨ s = 6) :
    faceSizes.count 5 + faceSizes.count 6 = faceSizes.length := by
  induction faceSizes with
  | nil => simp
  | cons a t ih =>
    have ha := pentOrHex a (by simp)
    have hi := ih fun s hs => pentOrHex s (by simp [hs])
    rcases ha with rfl | rfl <;> simp <;> omega

/-- In a list of face sizes all equal to `5` or `6`, the total number of edge–face
incidences is `5 * (number of pentagons) + 6 * (number of hexagons)`. -/
theorem five_mul_count_pentagons_add_six_mul_count_hexagons
    (faceSizes : List Nat) (pentOrHex : ∀ s ∈ faceSizes, s = 5 ∨ s = 6) :
    5 * faceSizes.count 5 + 6 * faceSizes.count 6 = faceSizes.sum := by
  induction faceSizes with
  | nil => simp
  | cons a t ih =>
    have ha := pentOrHex a (by simp)
    have hi := ih fun s hs => pentOrHex s (by simp [hs])
    rcases ha with rfl | rfl <;> simp <;> omega

/-- **Fullerene pentagon count, face-list form.**

Let a polyhedron have `V` vertices, `E` edges, and faces whose sizes are listed in
`faceSizes`.  If every face is a pentagon or a hexagon, Euler's formula holds, every
vertex is trivalent (`3 * V = 2 * E`), and the face sizes sum to `2 * E` (each edge
borders two faces), then exactly `12` of the faces are pentagons. -/
theorem fullerene_pentagons_of_faceSizes
    (V E : Nat) (faceSizes : List Nat)
    (pentOrHex : ∀ s ∈ faceSizes, s = 5 ∨ s = 6)
    (euler : V + faceSizes.length = E + 2)
    (trivalent : 3 * V = 2 * E)
    (edges : faceSizes.sum = 2 * E) :
    faceSizes.count 5 = 12 :=
  fullerene_pentagons V E faceSizes.length (faceSizes.count 5) (faceSizes.count 6)
    euler trivalent (count_pentagons_add_count_hexagons faceSizes pentOrHex)
    (by
      rw [five_mul_count_pentagons_add_six_mul_count_hexagons faceSizes pentOrHex]
      exact edges)

/-- Sanity check: the buckminsterfullerene C₆₀ data (`V = 60`, `E = 90`, twelve
pentagons and twenty hexagons) satisfies all the hypotheses, so the theorem is not
vacuous. -/
example : (List.replicate 12 5 ++ List.replicate 20 6 : List Nat).count 5 = 12 :=
  fullerene_pentagons_of_faceSizes 60 90 _
    (by
      intro s hs
      rcases List.mem_append.mp hs with h | h
      · exact Or.inl (List.eq_of_mem_replicate h)
      · exact Or.inr (List.eq_of_mem_replicate h))
    (by simp) (by omega) (by simp)

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

