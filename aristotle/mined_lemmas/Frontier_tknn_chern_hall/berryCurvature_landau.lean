import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

/-- The Berry curvature `F = ∂_{k₁} A₂ - ∂_{k₂} A₁` of a `U(1)` Berry connection
`(A₁, A₂)` on the Brillouin torus, written in coordinates. -/

lemma berryCurvature_landau (n : ℤ) (k₁ k₂ : ℝ) :
    berryCurvature (landauA₁ n) (landauA₂ n) k₁ k₂ = (n : ℝ) / (2 * Real.pi) := by
  have h1 : deriv (fun x : ℝ => landauA₂ n x k₂) k₁ = (n : ℝ) / (2 * Real.pi) := by
    simp only [landauA₂]
    rw [show (fun x : ℝ => (n : ℝ) * x / (2 * Real.pi))
        = fun x : ℝ => ((n : ℝ) / (2 * Real.pi)) * x by funext x; ring]
    have hd : HasDerivAt (fun x : ℝ => ((n : ℝ) / (2 * Real.pi)) * x)
        ((n : ℝ) / (2 * Real.pi)) k₁ := by
      simpa using (hasDerivAt_id k₁).const_mul ((n : ℝ) / (2 * Real.pi))
    exact hd.deriv
  have h2 : deriv (fun y : ℝ => landauA₁ n k₁ y) k₂ = 0 := by
    simp [landauA₁]
  simp [berryCurvature, h1, h2]

/-- **Key intermediate lemma (quantization).** The integral of the Berry curvature over the
Brillouin torus is `2π n`; equivalently the Chern number of the model is the integer `n`. -/
