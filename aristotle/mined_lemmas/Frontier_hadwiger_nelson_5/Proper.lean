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

/-!
# Basic notions for the Hadwiger–Nelson problem

We identify the Euclidean plane with `ℂ`.  A *proper* 4-colouring is a map
`c : ℂ → Fin 4` such that no two points at distance exactly `1` receive the
same colour.  We phrase the distance condition with `Complex.normSq` (the
squared modulus) so that all verifications stay polynomial.
-/

namespace CNP

open Complex

/-- A proper 4-colouring of the plane. -/

theorem Proper.affine {c : ℂ → Fin 4} (hc : Proper c) {u v : ℂ} (hu : normSq u = 1) :
    Proper fun z => c (u * z + v) := by
  intro z w h
  refine hc _ _ ?_
  have e : u * z + v - (u * w + v) = u * (z - w) := by ring
  rw [e, normSq_mul, hu, one_mul, h]

