import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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

namespace Phys

open Complex MeasureTheory intervalIntegral
open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Phases -/

/-- The unimodular phase `u ↦ exp (i r u)`. -/

theorem chi_deriv_split (P DP : ℝ → E →L[ℂ] E) (e₁ e₂ ε : ℝ) (ψ : ℝ → E)
    (hP : ∀ s, HasDerivAt P (DP s) s) (hidem : ∀ s, (P s).comp (P s) = P s)
    (hψ : ∀ s, HasDerivAt ψ ((-Complex.I / (ε : ℂ)) • (ham P e₁ e₂ s (ψ s))) s) (s : ℝ) :
    HasDerivAt (chi P e₂ ε ψ)
      (-(cphase ((e₂ - e₁) / ε) s • DP s (alph P e₁ ε ψ s)) - DP s (chi P e₂ ε ψ s)) s := by
  refine (chi_hasDerivAt P DP e₁ e₂ ε ψ hP hidem hψ s).congr_deriv ?_
  have h1 : DP s (alph P e₁ ε ψ s) = cphase (e₁ / ε) s • DP s (P s (ψ s)) := by
    rw [alph, ContinuousLinearMap.map_smul]
  have h2 : DP s (chi P e₂ ε ψ s) = cphase (e₂ / ε) s • DP s (ψ s - P s (ψ s)) := by
    rw [chi, ContinuousLinearMap.map_smul]
  have h3 : (e₂ - e₁) / ε + e₁ / ε = e₂ / ε := by ring
  rw [h1, h2, smul_smul, cphase_add, h3, map_sub, smul_sub]
  abel

/-! ## Bound on an oscillatory integral -/

/-- Nonstationary phase: an oscillatory integral of a `C¹` function is `O(1/ω)`. -/
