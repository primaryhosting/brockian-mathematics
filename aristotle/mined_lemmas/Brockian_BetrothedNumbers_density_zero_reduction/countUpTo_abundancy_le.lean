import Mathlib
/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Filter Finset

/-! ## Natural density -/

/-- The number of elements of `A` in the interval `[1, N]`. -/

lemma countUpTo_abundancy_le {K : ℝ} (hK : 0 < K) (N : ℕ) :
    (countUpTo {n | (K : ℝ) * n < sigmaOne n} N : ℝ) ≤ 2 * N / K := by
  set S : Finset ℕ := {n ∈ Finset.Icc 1 N | n ∈ {n : ℕ | (K : ℝ) * n < sigmaOne n}} with hS
  have hsub : S ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have key : (S.card : ℝ) * K ≤ ∑ n ∈ S, (sigmaOne n : ℝ) / n := by
    have hconst : (S.card : ℝ) * K = ∑ _n ∈ S, K := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [hS, Finset.mem_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn.1.1
    rw [le_div_iff₀ hn0]
    exact le_of_lt hn.2
  have hle : ∑ n ∈ S, (sigmaOne n : ℝ) / n ≤ ∑ n ∈ Finset.Icc 1 N, (sigmaOne n : ℝ) / n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  have h2 := sum_sigmaOne_div_le N
  have hfin : (S.card : ℝ) * K ≤ 2 * N := by linarith
  rw [le_div_iff₀ hK]
  simpa [countUpTo, hS] using hfin

/-- Uniform sparsity of the large-abundancy numbers. -/
