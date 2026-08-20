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

theorem schrodingerExpr_add (V₀ : ℝ) {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    schrodingerExpr V₀ (fun x => f x + g x)
      = fun x => schrodingerExpr V₀ f x + schrodingerExpr V₀ g x := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by simp)
  have hg1 : Differentiable ℝ g := hg.differentiable (by simp)
  have hf1' : Differentiable ℝ (deriv f) :=
    (by simpa using hf.iterate_deriv 1 : ContDiff ℝ (⊤ : ℕ∞) (deriv f)).differentiable (by simp)
  have hg1' : Differentiable ℝ (deriv g) :=
    (by simpa using hg.iterate_deriv 1 : ContDiff ℝ (⊤ : ℕ∞) (deriv g)).differentiable (by simp)
  have h1 : deriv (fun x => f x + g x) = fun x => deriv f x + deriv g x :=
    funext fun x => deriv_add (hf1 x) (hg1 x)
  have h2 : deriv (fun x => deriv f x + deriv g x)
      = fun x => deriv (deriv f) x + deriv (deriv g) x :=
    funext fun x => deriv_add (hf1' x) (hg1' x)
  funext x
  simp only [schrodingerExpr, h1, h2]
  ring

