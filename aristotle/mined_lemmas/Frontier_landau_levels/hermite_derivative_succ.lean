/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

noncomputable section

open Polynomial

/-! ## Probabilists' Hermite polynomials over `ℝ` -/

/-- The `n`-th probabilists' Hermite polynomial, with real coefficients. -/

theorem hermite_derivative_succ (n : ℕ) :
    derivative (hermite (n + 1)) = C ((n : ℤ) + 1) * hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, ih]
    simp only [derivative_X, one_mul, derivative_mul, derivative_C, zero_mul, zero_add]
    rw [hermite_succ n]
    push_cast [C_add, C_1]
    ring

