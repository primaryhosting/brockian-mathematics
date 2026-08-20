/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
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

/-- The Berry curvature of a Berry connection one-form `A = A₁ dx + A₂ dy` on the
(two–dimensional) parameter space `ℝ × ℝ`: it is the exterior derivative
`F = ∂₁A₂ - ∂₂A₁`. -/

theorem berryPhase_symmetric_gauge (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhase (fun p : ℝ × ℝ => -p.2 / 2) (fun p : ℝ × ℝ => p.1 / 2) a₁ a₂ b₁ b₂ =
      (b₁ - a₁) * (b₂ - a₂) := by
  have hA₁ : ContDiff ℝ 1 (fun p : ℝ × ℝ => -p.2 / 2) := (contDiff_snd.neg).div_const 2
  have hA₂ : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 / 2) := contDiff_fst.div_const 2
  have hcurv : ∀ p : ℝ × ℝ,
      berryCurvature (fun p : ℝ × ℝ => -p.2 / 2) (fun p : ℝ × ℝ => p.1 / 2) p = 1 := by
    intro p
    have h₂ : HasFDerivAt (fun q : ℝ × ℝ => q.1 / 2)
        ((2:ℝ)⁻¹ • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p := by
      simpa [div_eq_inv_mul] using (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_smul ((2:ℝ)⁻¹)
    have h₁ : HasFDerivAt (fun q : ℝ × ℝ => -q.2 / 2)
        (-((2:ℝ)⁻¹ • (ContinuousLinearMap.snd ℝ ℝ ℝ))) p := by
      simpa [div_eq_inv_mul, neg_div] using
        (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_smul ((2:ℝ)⁻¹)).neg)
    rw [berryCurvature, h₁.fderiv, h₂.fderiv]
    norm_num
  rw [berry_phase_quantized _ _ hA₁ hA₂]
  simp only [hcurv]
  simp
  ring

end Frontier

