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

lemma hasDerivAt_polyGauss (p : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => eval u p * Real.exp (-(u ^ 2 / 4)))
      (eval t (gDeriv p) * Real.exp (-(t ^ 2 / 4))) t := by
  have h1 : HasDerivAt (fun u : ℝ => eval u p) (eval t (derivative p)) t := p.hasDerivAt t
  have h2 : HasDerivAt (fun u : ℝ => -(u ^ 2 / 4)) (-(t / 2)) t := by
    have := ((hasDerivAt_pow 2 t).div_const 4).neg
    simpa using this
  have h3 := h2.exp
  have := h1.mul h3
  convert this using 1
  simp [gDeriv]
  ring

