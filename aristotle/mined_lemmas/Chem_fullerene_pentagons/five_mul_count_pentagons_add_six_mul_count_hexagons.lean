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
