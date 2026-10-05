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

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Classical
open Filter MeasureTheory AddCircle

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The Cesàro average of `f` along the first `N` terms of the sequence `u`. -/

lemma tendsto_of_mem_span (u : ℕ → AddCircle T)
    (hu : ∀ m : ℤ, m ≠ 0 → Tendsto (avg u (fourier m)) atTop (nhds 0))
    (f : C(AddCircle T, ℂ)) (hf : f ∈ Submodule.span ℂ (Set.range (@fourier T))) :
    Tendsto (avg u f) atTop (nhds (∫ x, f x ∂(@haarAddCircle T hT))) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨m, rfl⟩ := hg
      rcases eq_or_ne m 0 with rfl | hm
      · have hint : ∫ x, (fourier (0 : ℤ) x : ℂ) ∂(@haarAddCircle T hT) = 1 := by
          simp
        rw [hint]
        have heq : (fun _ : ℕ => (1 : ℂ)) =ᶠ[atTop] avg u (fourier (0 : ℤ)) := by
          filter_upwards [eventually_ge_atTop 1] with N hN
          have hN0 : (N : ℂ) ≠ 0 := by
            simpa using (Nat.pos_of_ne_zero (by omega) : 0 < N).ne'
          simp [avg, hN0]
        exact Tendsto.congr' heq tendsto_const_nhds
      · rw [integral_fourier_ne_zero hm]
        exact hu m hm
  | zero =>
      have h0 : avg u (0 : C(AddCircle T, ℂ)) = fun _ : ℕ => (0 : ℂ) := by
        funext N; simp [avg]
      rw [h0]
      simp only [ContinuousMap.zero_apply, integral_zero]
      exact tendsto_const_nhds
  | add g h _ _ ihg ihh =>
      have hint : ∫ x, ((g + h) x : ℂ) ∂(@haarAddCircle T hT)
          = (∫ x, g x ∂(@haarAddCircle T hT)) + ∫ x, h x ∂(@haarAddCircle T hT) := by
        simpa using integral_add (integrable_contMap g) (integrable_contMap h)
      rw [hint, funext (avg_add u g h)]
      exact ihg.add ihh
  | smul c g _ ih =>
      have hint : ∫ x, ((c • g) x : ℂ) ∂(@haarAddCircle T hT)
          = c * ∫ x, g x ∂(@haarAddCircle T hT) := by
        simpa [smul_eq_mul] using integral_smul c (fun x => g x) (μ := (@haarAddCircle T hT))
      rw [hint, funext (avg_smul u c g)]
      exact ih.const_mul c

/-- **Weyl's equidistribution criterion.**  If, for every nonzero frequency `m`, the Cesàro
averages of the character `fourier m` along the sequence `u : ℕ → AddCircle T` tend to `0`,
then the sequence is equidistributed: for every continuous `f : AddCircle T → ℂ`, the Cesàro
averages of `f` along `u` converge to the mean value of `f` with respect to normalized Haar
measure. -/
