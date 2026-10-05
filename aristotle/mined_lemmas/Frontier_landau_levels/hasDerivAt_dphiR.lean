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

open Polynomial

/-! ## Hermite polynomials over `ℝ` -/

/-- The (probabilists') Hermite polynomials, with real coefficients. -/

theorem hasDerivAt_dphiR (hhbar : 0 < hbar) (hqB : 0 < q * B) (x : ℝ) :
    HasDerivAt (dphiR hbar q B k n) (ddphiR hbar q B k n x) x := by
  have hL : landauL hbar q B ≠ 0 := (landauL_pos hhbar hqB).ne'
  have haff : HasDerivAt (fun t : ℝ => (t - landauX0 hbar q B k) / landauL hbar q B)
      (1 / landauL hbar q B) x := by
    have := ((hasDerivAt_id x).sub_const (landauX0 hbar q B k)).div_const (landauL hbar q B)
    simpa using this
  have h := ((hasDerivAt_chi1 n ((x - landauX0 hbar q B k) / landauL hbar q B)).comp x
    haff).const_mul (1 / landauL hbar q B)
  unfold dphiR ddphiR
  simpa [Function.comp, sq, mul_comm, mul_assoc, mul_left_comm] using h


/-! ### Unfolding lemmas for the momentum operators -/

