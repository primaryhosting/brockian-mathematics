/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Topology

namespace Brockian

/-- The local factor deficiency `1/(p-1)^2` occurring in the twin-prime singular series. -/

lemma tailProd_bounds {M N : ℕ} (h2 : 2 ≤ M) :
    0 ≤ tailProd M N ∧ tailProd M N ≤ 1 ∧ 1 - 1 / ((M : ℝ) - 1) ≤ tailProd M N := by
  classical
  set T := (Finset.Ico (M + 1) (N + 1)).filter Nat.Prime with hT
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2
  have hterms0 : ∀ p ∈ T, 0 ≤ singularTerm p := fun p _ => singularTerm_nonneg p
  have hterms1 : ∀ p ∈ T, singularTerm p ≤ 1 := by
    intro p hp
    simp only [hT, Finset.mem_filter, Finset.mem_Ico] at hp
    exact singularTerm_le_one (by omega)
  refine ⟨Finset.prod_nonneg fun p hp => by have := hterms1 p hp; linarith,
    Finset.prod_le_one (fun p hp => by have := hterms1 p hp; linarith)
      (fun p hp => by have := hterms0 p hp; linarith), ?_⟩
  have hsumT : ∑ p ∈ T, singularTerm p ≤ 1 / ((M : ℝ) - 1) := by
    rcases le_or_gt M N with hMN | hMN
    · have h1 : ∑ p ∈ T, singularTerm p ≤ ∑ n ∈ Finset.Ico (M + 1) (N + 1), singularTerm n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => singularTerm_nonneg i)
      have h2' := sum_singularTerm_le (a := M + 1) (b := N + 1) (by omega) (by omega)
      have hcast : ((M + 1 : ℕ) : ℝ) - 2 = (M : ℝ) - 1 := by push_cast; ring
      have hNR : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
      have hpos : 0 < 1 / (((N + 1 : ℕ) : ℝ) - 2) := by
        have : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) - 2 := by push_cast; linarith
        positivity
      rw [hcast] at h2'
      linarith
    · have hempty : T = ∅ := by
        rw [hT, Finset.Ico_eq_empty (by omega), Finset.filter_empty]
      have hbnd0 : 0 ≤ 1 / ((M : ℝ) - 1) := by
        have : (0 : ℝ) < (M : ℝ) - 1 := by linarith
        positivity
      rw [hempty]
      simpa using hbnd0
  have := one_sub_sum_le_prod_one_sub hterms0 hterms1
  unfold tailProd
  rw [← hT]
  linarith

/-- Splitting the truncated product at level `M`. -/
