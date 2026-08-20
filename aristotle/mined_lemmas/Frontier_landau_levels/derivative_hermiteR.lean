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

lemma derivative_hermiteR (n : ℕ) :
    derivative (hermiteR (n + 1)) = C ((n : ℝ) + 1) * hermiteR n := by
  induction n with
  | zero => simp [hermiteR_one, hermiteR_zero]
  | succ n ih =>
      rw [hermiteR_succ (n + 1)]
      rw [derivative_sub, derivative_mul, derivative_X, ih]
      rw [derivative_C_mul]
      have h : hermiteR (n + 1) = X * hermiteR n - derivative (hermiteR n) := hermiteR_succ n
      push_cast
      rw [h]
      ring
  
/-- The Hermite differential equation `He_n'' - x He_n' + n He_n = 0`. -/
