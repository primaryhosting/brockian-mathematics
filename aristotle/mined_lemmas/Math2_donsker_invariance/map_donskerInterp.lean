/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Math2

/-- The linearly interpolated, rescaled random walk
`W_n(t) = (S_{⌊nt⌋} + (nt - ⌊nt⌋) X_{⌊nt⌋}) / √n`, where `S_m = X_0 + ⋯ + X_{m-1}`.
This is the classical Donsker polygonal process associated to the steps `X`. -/

lemma map_donskerInterp {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) (n : ℕ) (t : ℝ) :
    P.map (donskerInterp X n t) = gaussianReal 0 (donskerVar n t) := by
  set m := ⌊(n : ℝ) * t⌋₊ with hm
  set th := (n : ℝ) * t - m with hth
  have hthnn : (0:ℝ) ≤ th ^ 2 := sq_nonneg _
  have hfrac : P.map (fun ω ↦ th * X m ω) = gaussianReal 0 ⟨th ^ 2, hthnn⟩ := by
    rw [show (fun ω ↦ th * X m ω) = (fun x ↦ th * x) ∘ (X m) from rfl,
      ← Measure.map_map (by fun_prop) (hmeas m), hlaw m, gaussianReal_map_const_mul]
    norm_num
  have heq : (∑ j ∈ Finset.range m, X j) = fun ω ↦ ∑ i ∈ Finset.range m, X i ω := by
    funext ω; simp [Finset.sum_apply]
  have hind : IndepFun (fun ω ↦ ∑ i ∈ Finset.range m, X i ω) (fun ω ↦ th * X m ω) P := by
    have h := hindep.indepFun_finset_sum_of_notMem hmeas (s := Finset.range m) (i := m) (by simp)
    rw [heq] at h
    exact h.comp measurable_id (by fun_prop)
  have hY : P.map (fun ω ↦ (∑ i ∈ Finset.range m, X i ω) + th * X m ω)
      = gaussianReal 0 ((m : ℝ≥0) + ⟨th ^ 2, hthnn⟩) := by
    have h := gaussianReal_add_gaussianReal_of_indepFun hind
      (map_partialSum hmeas hindep hlaw m) hfrac
    simpa [Pi.add_def] using h
  have hcomp : donskerInterp X n t
      = (fun x ↦ (Real.sqrt n)⁻¹ * x) ∘ (fun ω ↦ (∑ i ∈ Finset.range m, X i ω) + th * X m ω) := by
    funext ω; simp [donskerInterp, div_eq_inv_mul, hm, hth]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), hY, gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    have h1 : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    push_cast
    rw [donskerVar, Real.coe_toNNReal _ (by positivity), h1, ← hm, ← hth]
    ring

/-- The variance of the rescaled walk at time `t` converges to `t`. -/
