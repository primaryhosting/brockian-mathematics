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

theorem He_ode (n : ℕ) (x : ℝ) : He'' n x = x * He' n x - n * He n x := by
  cases n with
  | zero => simp [He'', He', He, Herm]
  | succ m =>
    have h1 : He'' (m + 1) x = ((m : ℝ) + 1) * He' m x := by
      simp [He'', He', derivative_Herm_succ m]
    rw [h1, He'_succ, He_succ]
    push_cast
    ring

/-! ## Hermite (Gauss-weighted) functions with length scale `s` -/

/-- The `n`-th Hermite function with length scale `s`:
`u ↦ He n (u/s) * exp (-(u/s)^2/4)`. -/
