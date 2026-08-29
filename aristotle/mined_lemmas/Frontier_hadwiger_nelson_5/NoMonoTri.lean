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

theorem NoMonoTri.affine {c : ℂ → Fin 4} (hc : NoMonoTri c) {u v : ℂ} (hu : normSq u = 1) :
    NoMonoTri fun z => c (u * z + v) := by
  intro p q r h1 h2 h3
  have e1 : u * p + v - (u * q + v) = u * (p - q) := by ring
  have e2 : u * q + v - (u * r + v) = u * (q - r) := by ring
  have e3 : u * p + v - (u * r + v) = u * (p - r) := by ring
  refine hc _ _ _ ?_ ?_ ?_
  · rw [e1, normSq_mul, hu, one_mul, h1]
  · rw [e2, normSq_mul, hu, one_mul, h2]
  · rw [e3, normSq_mul, hu, one_mul, h3]

/-- Planar algebra: two vectors orthogonal to a common nonzero vector and of equal length
are equal or opposite. -/
