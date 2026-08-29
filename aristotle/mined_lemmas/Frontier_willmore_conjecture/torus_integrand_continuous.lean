/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Real

/-! ## Partial derivatives of functions of two real variables -/

/-- Partial derivative with respect to the first variable. -/

lemma torus_integrand_continuous (hr : 0 < r) (hR : r < R) :
    Continuous (fun u : ℝ => (R + 2 * r * cos u) ^ 2 / (4 * r * (R + r * cos u))) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  have hw : 0 < R + r * cos x := by nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x]
  positivity

/-- The integral of the Willmore integrand over one period in `u`. -/
