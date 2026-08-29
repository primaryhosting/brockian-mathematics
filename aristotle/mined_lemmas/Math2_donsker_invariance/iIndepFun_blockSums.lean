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

lemma iIndepFun_blockSums {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {k N : ℕ} (s : Fin k → Finset ℕ) (hsub : ∀ j, s j ⊆ Finset.range N)
    (hs : Pairwise (Function.onFun Disjoint s)) :
    iIndepFun (fun j ω ↦ ∑ i ∈ s j, X i ω) P := by
  classical
  let L : (Fin N → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
    LinearMap.pi fun j ↦ ∑ i : Fin N, if (i : ℕ) ∈ s j then LinearMap.proj i else 0
  have hL : ∀ (v : Fin N → ℝ) (j : Fin k),
      L v j = ∑ i : Fin N, if (i : ℕ) ∈ s j then v i else 0 := by
    intro v j
    simp only [L, LinearMap.pi_apply, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  set L' := LinearMap.toContinuousLinearMap L with hL'
  have hgauss : HasGaussianLaw (fun ω (i : Fin N) ↦ X i ω) P := by
    refine iIndepFun.hasGaussianLaw (fun i ↦ ?_) (hindep.precomp Fin.val_injective)
    exact ⟨by rw [hlaw]; infer_instance⟩
  have hDeq : (fun ω (j : Fin k) ↦ ∑ i ∈ s j, X i ω) = fun ω ↦ L' (fun i : Fin N ↦ X i ω) := by
    funext ω j
    change ∑ i ∈ s j, X i ω = L (fun i : Fin N ↦ X i ω) j
    rw [hL, Fin.sum_univ_eq_sum_range (fun i ↦ if i ∈ s j then X i ω else 0) N,
      Finset.sum_ite_mem]
    congr 1
    exact (Finset.inter_eq_right.2 (hsub j)).symm
  have hDg : HasGaussianLaw (fun ω (j : Fin k) ↦ ∑ i ∈ s j, X i ω) P := by
    rw [hDeq]; exact hgauss.map_fun L'
  refine hDg.iIndepFun_of_covariance_eq_zero fun a b hab ↦ ?_
  have hpair : IndepFun (fun ω ↦ ∑ i ∈ s a, X i ω) (fun ω ↦ ∑ i ∈ s b, X i ω) P := by
    have h := hindep.indepFun_finset (s a) (s b) (hs hab) hmeas
    have h2 := h.comp (φ := fun v : (s a) → ℝ ↦ ∑ i, v i) (ψ := fun v : (s b) → ℝ ↦ ∑ i, v i)
      (by fun_prop) (by fun_prop)
    simpa [Function.comp_def, fun ω ↦ Finset.sum_attach (s a) fun i ↦ X i ω,
      fun ω ↦ Finset.sum_attach (s b) fun i ↦ X i ω] using h2
  exact hpair.covariance_eq_zero (hDg.eval a).memLp_two (hDg.eval b).memLp_two

