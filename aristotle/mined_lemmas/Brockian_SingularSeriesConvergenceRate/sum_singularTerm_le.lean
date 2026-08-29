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

lemma sum_singularTerm_le {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ∑ n ∈ Finset.Ico (N + 1) (M + 1), singularTerm n
      ≤ 1 / ((N : ℝ) - 1) - 1 / ((M : ℝ) - 1) := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
      have hM2 : (2 : ℝ) ≤ (M : ℝ) := by
        have : (2 : ℕ) ≤ M := le_trans hN hM
        exact_mod_cast this
      rw [Finset.sum_Ico_succ_top (by omega)]
      have hterm : singularTerm (M + 1) ≤ 1 / ((M : ℝ) - 1) - 1 / (((M : ℝ) + 1) - 1) := by
        unfold singularTerm
        have hcast : ((M + 1 : ℕ) : ℝ) - 1 = (M : ℝ) := by push_cast; ring
        rw [hcast]
        rw [div_sub_div _ _ (by linarith) (by linarith)]
        rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
        nlinarith
      have hcast2 : ((M + 1 : ℕ) : ℝ) - 1 = (M : ℝ) := by push_cast; ring
      rw [hcast2]
      have : (1 : ℝ) / (M : ℝ) = 1 / (((M : ℝ) + 1) - 1) := by ring_nf
      linarith [ih, hterm]

/-- Splitting the partial product at `N`. -/
