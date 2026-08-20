/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open Finset MeasureTheory Metric Module Real Set

/-! ## The Pfaffian of the curvature form of the unit round sphere -/

section Pfaffian

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- First index of the `i`-th pair `(2i, 2i+1)`. -/

theorem chern_gauss_bonnet_pfaffian (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : Fin (2 * m) → V) (c : ℝ)
    (hv : ExteriorAlgebra.ιMulti ℝ (2 * m) v ≠ 0)
    (hc : spherePfaffian m v = c • ExteriorAlgebra.ιMulti ℝ (2 * m) v) :
    (1 / (2 * π) ^ m) * c * sphereArea m = (simplicialSphereEulerChar m : ℝ) := by
  have hcval : c = ((2 * m)! / (2 ^ m * (m)!) : ℝ) := by
    by_contra hne
    apply hv
    have hzero : (c - ((2 * m)! / (2 ^ m * (m)!) : ℝ)) • ExteriorAlgebra.ιMulti ℝ (2 * m) v = 0 := by
      rw [sub_smul, ← hc, spherePfaffian_eq, sub_self]
    rcases smul_eq_zero.mp hzero with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hne
    · exact h1
  rw [hcval]
  exact chern_gauss_bonnet m

end Math2

