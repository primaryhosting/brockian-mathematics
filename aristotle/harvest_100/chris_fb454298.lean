/-!
# Fullerene Pentagons
Category: Chemistry
Target: Chem.fullerene_pentagons
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- **Fullerene pentagon count.**

A convex polyhedron (so Euler's formula `V - E + F = 2` holds) in which every vertex has
degree three (`3 * V = 2 * E`, the handshake lemma for vertices) and every face is either a
pentagon or a hexagon (`F = p + h` faces in total, with edge–face incidence
`2 * E = 5 * p + 6 * h`) has exactly `12` pentagonal faces.

This is the combinatorial fact underlying the structure of fullerenes such as C₆₀. -/
theorem fullerene_pentagons
    (V E F p h : Nat)
    (euler : V + F = E + 2)
    (trivalent : 3 * V = 2 * E)
    (faces : F = p + h)
    (edges : 2 * E = 5 * p + 6 * h) :
    p = 12 := by
  omega

/-- The hypotheses are consistent: the buckminsterfullerene C₆₀ realizes them,
with `V = 60`, `E = 90`, `F = 32`, `12` pentagons and `20` hexagons. -/
example : 60 + 32 = 90 + 2 ∧ 3 * 60 = 2 * 90 ∧ (32 : Nat) = 12 + 20 ∧ 2 * 90 = 5 * 12 + 6 * 20 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

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

