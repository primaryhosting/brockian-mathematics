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

theorem alph_hasDerivAt (P DP : ℝ → E →L[ℂ] E) (e₁ e₂ ε : ℝ) (ψ : ℝ → E)
    (hP : ∀ s, HasDerivAt P (DP s) s) (hidem : ∀ s, (P s).comp (P s) = P s)
    (hψ : ∀ s, HasDerivAt ψ ((-Complex.I / (ε : ℂ)) • (ham P e₁ e₂ s (ψ s))) s) (s : ℝ) :
    HasDerivAt (alph P e₁ ε ψ) (cphase (e₁ / ε) s • DP s (ψ s)) s := by
  have hu : HasDerivAt (fun t => P t (ψ t))
      (DP s (ψ s) + ((-Complex.I / (ε : ℂ)) * (e₁ : ℂ)) • P s (ψ s)) s := by
    refine hasDerivAt_clmApply P DP ψ _ _ s (hP s) (hψ s) ?_
    rw [ContinuousLinearMap.map_smul, proj_ham P e₁ e₂ s (hidem s), smul_smul]
  have h := (cphase_hasDerivAt (e₁ / ε) s).smul hu
  have heq : cphase (e₁ / ε) s • (DP s (ψ s) + ((-Complex.I / (ε : ℂ)) * (e₁ : ℂ)) • P s (ψ s))
      + (cphase (e₁ / ε) s * (((e₁ / ε : ℝ) : ℂ) * Complex.I)) • P s (ψ s)
      = cphase (e₁ / ε) s • DP s (ψ s) := by
    rw [smul_add, smul_smul, add_assoc, ← add_smul]
    have hz : cphase (e₁ / ε) s * ((-Complex.I / (ε : ℂ)) * (e₁ : ℂ))
        + cphase (e₁ / ε) s * (((e₁ / ε : ℝ) : ℂ) * Complex.I) = 0 := by
      push_cast
      ring
    rw [hz, zero_smul, add_zero]
  exact h.congr_deriv heq

