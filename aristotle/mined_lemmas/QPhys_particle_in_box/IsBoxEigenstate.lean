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

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well
of width `L`: `E n = n² π² ℏ² / (2 m L²)`. -/

def IsBoxEigenstate (m hbar L E : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧
    (∀ x : ℝ, -(hbar ^ 2 / (2 * m)) * deriv (deriv f) x = E * f x) ∧
    f 0 = 0 ∧ f L = 0 ∧ ∃ x ∈ Set.Ioo (0 : ℝ) L, f x ≠ 0

/-- For `f'' = -c f`, the quantity `(f')² + c f²` is constant. -/
