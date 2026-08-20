/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

open NormedSpace

namespace Frontier

section

variable {A : Type*} [CStarAlgebra A]

/-- A `ℚ`-normed-algebra structure, obtained by restricting scalars from `ℂ`; it is needed
to talk about `NormedSpace.exp` in a C⋆-algebra. -/
noncomputable local instance normedAlgebraRatOfCStarAlgebra : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℂ A

/-- `exp (t • H)` commutes with `H`. -/

lemma hasDerivAt_conj (H b : A) (s : ℝ) :
    HasDerivAt (fun r : ℝ => exp ((-r) • H) * b * exp (r • H))
      (exp ((-s) • H) * ⁅b, H⁆ * exp (s • H)) s := by
  have hneg : ∀ r : ℝ, exp ((-r) • H) = exp (r • (-H)) := by
    intro r; rw [neg_smul, smul_neg]
  have h1 : HasDerivAt (fun r : ℝ => exp (r • H)) (exp (s • H) * H) s :=
    hasDerivAt_exp_smul_const H s
  have h2 : HasDerivAt (fun r : ℝ => exp ((-r) • H)) (-(exp ((-s) • H) * H)) s := by
    have h := hasDerivAt_exp_smul_const (-H) s
    simp only [hneg]
    simpa [mul_neg] using h
  have h3 := (h2.mul_const b).mul h1
  refine h3.congr_deriv ?_
  have hc : exp (s • H) * H = H * exp (s • H) := commute_exp_smul H s
  rw [Ring.lie_def, hc]
  noncomm_ring

/-- Conjugation by the unitary `exp (-t • H)` preserves the norm. -/
