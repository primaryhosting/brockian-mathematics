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

theorem hasDerivAt_psi_mul_dpsi
    {psi dpsi ddpsi : ℝ → ℝ}
    (hpsi : ∀ x, HasDerivAt psi (dpsi x) x)
    (hdpsi : ∀ x, HasDerivAt dpsi (ddpsi x) x) (x : ℝ) :
    HasDerivAt (fun y => psi y * dpsi y) (dpsi x ^ 2 + psi x * ddpsi x) x := by
  have h := (hpsi x).mul (hdpsi x)
  convert h using 1
  ring

/-- Derivative of the virial function `Φ(x) = x (ψ'(x)² + (E - V(x)) ψ(x)²)`. -/
