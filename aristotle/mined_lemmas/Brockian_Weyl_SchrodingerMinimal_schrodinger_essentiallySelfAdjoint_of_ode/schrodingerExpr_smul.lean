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

/-
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Complex
open scoped Convolution

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Test functions and the minimal Schrödinger expression -/

/-- A test function on the line: smooth with compact support. -/

theorem schrodingerExpr_smul (V₀ : ℝ) (c : ℂ) {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    schrodingerExpr V₀ (fun x => c * f x) = fun x => c * schrodingerExpr V₀ f x := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by simp)
  have hf1' : Differentiable ℝ (deriv f) :=
    (by simpa using hf.iterate_deriv 1 : ContDiff ℝ (⊤ : ℕ∞) (deriv f)).differentiable (by simp)
  have h1 : deriv (fun x => c * f x) = fun x => c * deriv f x :=
    funext fun x => deriv_const_mul c (hf1 x)
  have h2 : deriv (fun x => c * deriv f x) = fun x => c * deriv (deriv f) x :=
    funext fun x => deriv_const_mul c (hf1' x)
  funext x
  simp only [schrodingerExpr, h1, h2]
  ring

/-! ## The range of `τ - z` as a subspace of `L²(ℝ)` -/

open scoped Classical in
/-- The class in `L²(ℝ)` of a function, when the function is square integrable. -/
