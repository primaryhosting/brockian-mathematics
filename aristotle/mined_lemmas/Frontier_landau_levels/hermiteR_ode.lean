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

lemma hermiteR_ode (n : ℕ) :
    derivative (derivative (hermiteR n)) - X * derivative (hermiteR n)
      + C (n : ℝ) * hermiteR n = 0 := by
  have h1 : derivative (hermiteR (n + 1)) = C ((n : ℝ) + 1) * hermiteR n := derivative_hermiteR n
  have h2 : hermiteR (n + 1) = X * hermiteR n - derivative (hermiteR n) := hermiteR_succ n
  rw [h2, derivative_sub, derivative_mul, derivative_X] at h1
  have hC : C ((n : ℝ) + 1) = C (n : ℝ) + 1 := by push_cast; ring
  rw [hC] at h1
  linear_combination -h1

/-! ## Gaussian-weighted derivative -/

/-- The polynomial factor obtained by differentiating `p(t) e^{-t²/4}`. -/
