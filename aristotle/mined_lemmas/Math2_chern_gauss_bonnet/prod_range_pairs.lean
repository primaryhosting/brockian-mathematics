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

theorem prod_range_pairs {M : Type*} [Monoid M] (m : ℕ) (a : ℕ → M) :
    ((List.range m).map (fun i => a (2 * i) * a (2 * i + 1))).prod
      = ((List.range (2 * m)).map a).prod := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [h2, List.range_succ, List.map_append, List.prod_append, List.range_succ,
      List.map_append, List.prod_append]
    simp [mul_assoc]

