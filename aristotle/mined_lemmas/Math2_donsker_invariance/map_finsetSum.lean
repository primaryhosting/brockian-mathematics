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

lemma map_finsetSum {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) (s : Finset ℕ) :
    P.map (fun ω ↦ ∑ i ∈ s, X i ω) = gaussianReal 0 s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Measure.map_const, gaussianReal_zero_var]
  | insert a s ha ih =>
    have hsum : (fun ω ↦ ∑ i ∈ insert a s, X i ω) = (fun ω ↦ ∑ i ∈ s, X i ω) + X a := by
      funext ω; simp [Finset.sum_insert ha, add_comm]
    have heq : (∑ j ∈ s, X j) = fun ω ↦ ∑ i ∈ s, X i ω := by
      funext ω; simp [Finset.sum_apply]
    have hind : IndepFun (fun ω ↦ ∑ i ∈ s, X i ω) (X a) P := by
      have h := hindep.indepFun_finset_sum_of_notMem hmeas (s := s) (i := a) ha
      rwa [heq] at h
    rw [hsum, gaussianReal_add_gaussianReal_of_indepFun hind ih (hlaw a)]
    congr 1
    · simp
    · rw [Finset.card_insert_of_notMem ha]; push_cast; ring

/-- Sums of an independent family of Gaussian variables over pairwise disjoint blocks are
mutually independent. -/
