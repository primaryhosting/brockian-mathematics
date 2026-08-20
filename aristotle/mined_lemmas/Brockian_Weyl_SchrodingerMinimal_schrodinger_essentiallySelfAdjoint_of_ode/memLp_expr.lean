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

theorem memLp_expr (V₀ : ℝ) (z : ℂ) {f : ℝ → ℂ} (hf : IsTestFunction f) :
    MemLp (fun x => schrodingerExpr V₀ f x - z * f x) 2 volume := by
  obtain ⟨hs, hc⟩ := hf
  have hs'' : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv f)) := by simpa using hs.iterate_deriv 2
  apply Continuous.memLp_of_hasCompactSupport
  · exact (hs''.continuous.neg.add (continuous_const.mul hs.continuous)).sub
      (continuous_const.mul hs.continuous)
  · exact HasCompactSupport.sub (HasCompactSupport.add hc.deriv.deriv.neg hc.mul_left) hc.mul_left

/-- The range of `τ - z` applied to test functions, as a subspace of `L²(ℝ)`. -/
