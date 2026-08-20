/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module doc-comment, so the header above is
-- reproduced verbatim as a module doc-comment immediately after the import.)
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

lemma gDeriv_gDeriv_hermiteR (n : ℕ) :
    gDeriv (gDeriv (hermiteR n))
      = (C (1 / 4) * X ^ 2 - C (n : ℝ) - C (1 / 2)) * hermiteR n := by
  have h := hermiteR_ode n
  simp only [gDeriv, derivative_sub, derivative_mul, derivative_X, derivative_C, Polynomial.map_one]
  linear_combination h

/-! ## The Hermite functions -/

/-- The `n`-th Hermite function `He_n(t) e^{-t²/4}` (unnormalised). -/
