/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Statement: For a bound stationary state, 2⟨T⟩ = ⟨r·∇V⟩ (quantum virial theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology

namespace Phys

/-- **Auxiliary integration-by-parts fact.**  If `f` is everywhere differentiable with
integrable derivative `f'` and `f` tends to `0` at both ends of the real line, then the
integral of `f'` over `ℝ` vanishes. -/

theorem integral_deriv_eq_zero_of_tendsto_zero
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Integrable f' volume)
    (hbot : Tendsto f atBot (𝓝 0)) (htop : Tendsto f atTop (𝓝 0)) :
    ∫ x, f' x = 0 := by
  simpa using MeasureTheory.integral_of_hasDerivAt_of_tendsto hf hf' hbot htop

/-- Derivative of the "current" `ψ ψ'`. -/
