/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The local (Euler) factor of the twin-prime singular series at `p`:
`1 - 1/(p-1)^2` at odd primes, and `1` at all other natural numbers. -/

lemma singularPartial_lower {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    singularPartial N - 1 / ((N : ℝ) - 1) ≤ singularPartial M := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hMr : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_trans hN hNM)
    linarith
  set T : ℝ := ∏ p ∈ Finset.Ico (N + 1) (M + 1), singularFactor p with hT
  have hlow : 1 - ∑ n ∈ Finset.Ico (N + 1) (M + 1), singularTerm n ≤ T := by
    have hstep : (1 - ∑ n ∈ Finset.Ico (N + 1) (M + 1), singularTerm n)
        ≤ ∏ n ∈ Finset.Ico (N + 1) (M + 1), (1 - singularTerm n) := by
      refine one_sub_sum_le_prod_one_sub _ _ (fun i _ => singularTerm_nonneg i) ?_
      intro i hi
      have : 3 ≤ i := by have := (Finset.mem_Ico.mp hi).1; omega
      linarith [singularTerm_le_quarter this]
    refine le_trans hstep ?_
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      have : 3 ≤ i := by have := (Finset.mem_Ico.mp hi).1; omega
      linarith [singularTerm_le_quarter this]
    · intro i hi
      exact one_sub_singularTerm_le_singularFactor (by have := (Finset.mem_Ico.mp hi).1; omega)
  have hsum : ∑ n ∈ Finset.Ico (N + 1) (M + 1), singularTerm n ≤ 1 / ((N : ℝ) - 1) := by
    have h := sum_singularTerm_le (by omega : 2 ≤ N) hNM
    have : (0:ℝ) ≤ 1 / ((M : ℝ) - 1) := by positivity
    linarith
  have hPN0 := singularPartial_nonneg N
  have hPN1 := singularPartial_le_one N
  have hsum0 : 0 ≤ ∑ n ∈ Finset.Ico (N + 1) (M + 1), singularTerm n :=
    Finset.sum_nonneg (fun i _ => singularTerm_nonneg i)
  rw [singularPartial_split (by omega : 2 ≤ N) hNM, ← hT]
  nlinarith [hlow, hsum, hPN0, hPN1, hsum0]

/-- **Singular series convergence rate.**  The partial products of the twin-prime
singular series converge to a positive limit `S`, with the effective rate
`|singularPartial N - S| ≤ 2 / N`. -/
