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

lemma map_partialSum {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) (m : ℕ) :
    P.map (fun ω ↦ ∑ i ∈ Finset.range m, X i ω) = gaussianReal 0 m := by
  induction m with
  | zero => simp [Measure.map_const, gaussianReal_zero_var]
  | succ m ih =>
    have hsum : (fun ω ↦ ∑ i ∈ Finset.range (m + 1), X i ω)
        = (fun ω ↦ ∑ i ∈ Finset.range m, X i ω) + X m := by
      funext ω; simp [Finset.sum_range_succ]
    rw [hsum]
    have heq : (∑ j ∈ Finset.range m, X j) = fun ω ↦ ∑ i ∈ Finset.range m, X i ω := by
      funext ω; simp [Finset.sum_apply]
    have hind : IndepFun (fun ω ↦ ∑ i ∈ Finset.range m, X i ω) (X m) P := by
      have h := hindep.indepFun_finset_sum_of_notMem hmeas (s := Finset.range m) (i := m) (by simp)
      rwa [heq] at h
    rw [gaussianReal_add_gaussianReal_of_indepFun hind ih (hlaw m)]
    congr 1
    · simp
    · push_cast; ring

/-- The law of the rescaled interpolated walk is centred Gaussian with variance
`(⌊nt⌋ + (nt - ⌊nt⌋)²)/n`. -/
