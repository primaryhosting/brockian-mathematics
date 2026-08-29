import Mathlib
/-!
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
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

namespace Phys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The map `λ ↦ H λ (ψ λ)` is differentiable, with the expected product rule, where the
operators `H λ` are `ℂ`-linear but the parameter `λ` is real. -/

theorem hasDerivAt_apply_of_hasDerivAt
    {H : ℝ → V →L[ℂ] V} {dH : V →L[ℂ] V} {psi : ℝ → V} {dpsi : V} {t : ℝ}
    (hH : HasDerivAt H dH t) (hpsi : HasDerivAt psi dpsi t) :
    HasDerivAt (fun l => H l (psi l)) (dH (psi t) + H t dpsi) t := by
  have hK : HasDerivAt (fun l => (H l).restrictScalars ℝ) (dH.restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hH
  exact hK.clm_apply hpsi

/-- If a curve stays on the unit sphere (in the sense that `⟪ψ λ, ψ λ⟫ = 1` for all `λ`), then
its velocity is "orthogonal" to it: `⟪ψ, ψ'⟫ + ⟪ψ', ψ⟫ = 0`. -/
