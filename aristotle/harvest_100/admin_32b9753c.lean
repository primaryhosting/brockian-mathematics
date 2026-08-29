/-!
# Fullerene Pentagons
Category: Chemistry
Target: Chem.fullerene_pentagons
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- **Fullerene pentagon count.**

A convex polyhedron whose every vertex has degree `3` (trivalent) and whose faces are all
pentagons or hexagons has exactly `12` pentagonal faces.

The combinatorial data is:
* `V`, `E`, `F` : the numbers of vertices, edges and faces;
* `P`, `H` : the numbers of pentagonal and hexagonal faces.

The hypotheses are Euler's formula `V - E + F = 2` (written additively, `V + F = E + 2`, to
avoid truncated natural subtraction), trivalence `3 * V = 2 * E` (the handshake lemma: every
vertex lies on exactly three edges and every edge has two ends), the face split `F = P + H`,
and the face handshake `5 * P + 6 * H = 2 * E` (every edge borders exactly two faces).

Conclusion: `P = 12`. Note that the number `H` of hexagons is *not* determined. -/
theorem fullerene_pentagons
    (V E F P H : Nat)
    (euler : V + F = E + 2)
    (trivalent : 3 * V = 2 * E)
    (faces : F = P + H)
    (edges_faces : 5 * P + 6 * H = 2 * E) :
    P = 12 := by
  omega

/-- Auxiliary counting fact: if every entry of a list of face sizes is `5` or `6`, then the
list splits into its pentagons and hexagons, both in length and in total size. -/
theorem length_and_sum_of_pentagon_hexagon_list :
    ∀ (L : List Nat), (∀ x ∈ L, x = 5 ∨ x = 6) →
      L.length = L.countP (· == 5) + L.countP (· == 6) ∧
        L.sum = 5 * L.countP (· == 5) + 6 * L.countP (· == 6)
  | [], _ => by simp
  | a :: L, h => by
    have hL : ∀ x ∈ L, x = 5 ∨ x = 6 := fun x hx => h x (List.mem_cons_of_mem a hx)
    obtain ⟨h1, h2⟩ := length_and_sum_of_pentagon_hexagon_list L hL
    rcases h a (List.mem_cons_self ..) with rfl | rfl <;>
      simp [h1, h2] <;> omega

/-- **Fullerene pentagon count, face-list form.**

Here the faces are given as a list `L` of face sizes, each of which is `5` or `6`.
Under Euler's formula, trivalence, and the face handshake relation, exactly `12` of the
faces are pentagons. -/
theorem fullerene_pentagons_list
    (V E : Nat) (L : List Nat)
    (hsizes : ∀ x ∈ L, x = 5 ∨ x = 6)
    (euler : V + L.length = E + 2)
    (trivalent : 3 * V = 2 * E)
    (edges_faces : L.sum = 2 * E) :
    L.countP (· == 5) = 12 := by
  obtain ⟨h1, h2⟩ := length_and_sum_of_pentagon_hexagon_list L hsizes
  exact fullerene_pentagons V E L.length _ _ (by omega) trivalent h1 (by omega)

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

