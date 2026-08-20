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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology AddCircle

namespace Brockian.Equidistribution

/-- The Cesàro (Birkhoff) average of `f` along the first `N` terms of the sequence `x`. -/

lemma tendsto_cesaroAvg_of_mem_span (x : ℕ → AddCircle (1 : ℝ))
    (hx : ∀ k : ℤ, k ≠ 0 → Tendsto (cesaroAvg x (fourier k)) atTop (𝓝 0))
    (g : C(AddCircle (1 : ℝ), ℂ)) (hg : g ∈ Submodule.span ℂ (Set.range (fourier (T := 1)))) :
    Tendsto (cesaroAvg x g) atTop (𝓝 (∫ t, g t ∂(haarAddCircle (T := 1)))) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, rfl⟩ := hg
      rcases eq_or_ne k 0 with rfl | hk
      · have hint : ∫ t, (fourier (T := 1) 0 t : ℂ) ∂(haarAddCircle (T := 1)) = 1 := by simp
        rw [hint]
        refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)))
        filter_upwards [eventually_ge_atTop 1] with N hN
        exact (cesaroAvg_fourier_zero x hN).symm
      · rw [integral_fourier_eq_zero hk]
        exact hx k hk
  | zero =>
      rw [cesaroAvg_zero]
      simp
  | add g₁ g₂ _ _ ih₁ ih₂ =>
      rw [show cesaroAvg x (⇑(g₁ + g₂)) = fun N => cesaroAvg x g₁ N + cesaroAvg x g₂ N from
        funext (cesaroAvg_add x g₁ g₂)]
      have hint : ∫ t, (g₁ + g₂) t ∂(haarAddCircle (T := 1))
          = (∫ t, g₁ t ∂(haarAddCircle (T := 1))) + ∫ t, g₂ t ∂(haarAddCircle (T := 1)) := by
        simp only [ContinuousMap.coe_add, Pi.add_apply]
        exact integral_add (integrable_continuous g₁) (integrable_continuous g₂)
      rw [hint]
      exact ih₁.add ih₂
  | smul c g _ ih =>
      rw [show cesaroAvg x (⇑(c • g)) = fun N => c * cesaroAvg x g N from
        funext (cesaroAvg_smul x c g)]
      have hint : ∫ t, (c • g) t ∂(haarAddCircle (T := 1))
          = c * ∫ t, g t ∂(haarAddCircle (T := 1)) := by
        simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact MeasureTheory.integral_const_mul c _
      rw [hint]
      exact ih.const_mul c

/-- Elements of the span of the Fourier characters are sup-norm dense in `C(ℝ/ℤ, ℂ)`. -/
