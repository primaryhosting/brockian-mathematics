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

theorem chi_hasDerivAt (P DP : ℝ → E →L[ℂ] E) (e₁ e₂ ε : ℝ) (ψ : ℝ → E)
    (hP : ∀ s, HasDerivAt P (DP s) s) (hidem : ∀ s, (P s).comp (P s) = P s)
    (hψ : ∀ s, HasDerivAt ψ ((-Complex.I / (ε : ℂ)) • (ham P e₁ e₂ s (ψ s))) s) (s : ℝ) :
    HasDerivAt (chi P e₂ ε ψ) (-(cphase (e₂ / ε) s • DP s (ψ s))) s := by
  set c : ℂ := -Complex.I / (ε : ℂ) with hc
  have hu : HasDerivAt (fun t => P t (ψ t)) (DP s (ψ s) + P s (c • ham P e₁ e₂ s (ψ s))) s :=
    hasDerivAt_clmApply P DP ψ _ _ s (hP s) (hψ s) rfl
  have hw : HasDerivAt (fun t => ψ t - P t (ψ t))
      ((c * (e₂ : ℂ)) • (ψ s - P s (ψ s)) - DP s (ψ s)) s := by
    refine ((hψ s).sub hu).congr_deriv ?_
    have h1 : P s (c • ham P e₁ e₂ s (ψ s)) = c • P s (ham P e₁ e₂ s (ψ s)) :=
      ContinuousLinearMap.map_smul _ _ _
    rw [h1]
    have h2 : ham P e₁ e₂ s (ψ s) - P s (ham P e₁ e₂ s (ψ s)) = (e₂ : ℂ) • (ψ s - P s (ψ s)) :=
      compl_ham P e₁ e₂ s (hidem s) (ψ s)
    have h3 : c • ham P e₁ e₂ s (ψ s) - (DP s (ψ s) + c • P s (ham P e₁ e₂ s (ψ s)))
        = c • (ham P e₁ e₂ s (ψ s) - P s (ham P e₁ e₂ s (ψ s))) - DP s (ψ s) := by
      rw [smul_sub]; abel
    rw [h3, h2, smul_smul]
  have h := (cphase_hasDerivAt (e₂ / ε) s).smul hw
  have heq : cphase (e₂ / ε) s • ((c * (e₂ : ℂ)) • (ψ s - P s (ψ s)) - DP s (ψ s))
      + (cphase (e₂ / ε) s * (((e₂ / ε : ℝ) : ℂ) * Complex.I)) • (ψ s - P s (ψ s))
      = -(cphase (e₂ / ε) s • DP s (ψ s)) := by
    rw [smul_sub, smul_smul]
    have hz : cphase (e₂ / ε) s * (c * (e₂ : ℂ))
        + cphase (e₂ / ε) s * (((e₂ / ε : ℝ) : ℂ) * Complex.I) = 0 := by
      rw [hc]; push_cast; ring
    have : cphase (e₂ / ε) s • ((c * (e₂ : ℂ)) • (ψ s - P s (ψ s))) - cphase (e₂ / ε) s • DP s (ψ s)
        + (cphase (e₂ / ε) s * (((e₂ / ε : ℝ) : ℂ) * Complex.I)) • (ψ s - P s (ψ s))
        = ((cphase (e₂ / ε) s * (c * (e₂ : ℂ)))
            + cphase (e₂ / ε) s * (((e₂ / ε : ℝ) : ℂ) * Complex.I)) • (ψ s - P s (ψ s))
          - cphase (e₂ / ε) s • DP s (ψ s) := by
      rw [add_smul, smul_smul]; abel
    rw [smul_smul] at this
    rw [this, hz, zero_smul, zero_sub]
  exact h.congr_deriv heq

/-- Splitting the derivative of the transverse component into an oscillatory source term and a
term proportional to the transverse component itself. -/
