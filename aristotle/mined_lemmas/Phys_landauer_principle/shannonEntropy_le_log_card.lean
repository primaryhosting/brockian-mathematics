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
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

/-- Shannon entropy (in nats) of a finite probability vector `p`. -/

theorem shannonEntropy_le_log_card {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : shannonEntropy p ≤ Real.log n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hsum
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- termwise version of `log x ≤ x - 1` applied to `x = 1 / (n * p i)`
  have key : ∀ i : Fin n, -(p i * Real.log (p i)) - p i * Real.log n ≤ 1 / n - p i := by
    intro i
    rcases eq_or_lt_of_le (hp i) with h | h
    · rw [← h]; simp
    · have hx : (0 : ℝ) < 1 / (n * p i) := by positivity
      have hlog := Real.log_le_sub_one_of_pos hx
      have h1 : Real.log (1 / (n * p i)) = -(Real.log n + Real.log (p i)) := by
        rw [Real.log_div one_ne_zero (by positivity),
          Real.log_mul (by positivity) (by positivity)]
        simp
      rw [h1] at hlog
      have h2 := mul_le_mul_of_nonneg_left hlog h.le
      have hpi : p i * (1 / (n * p i)) = 1 / n := by field_simp
      nlinarith [h2, hpi]
  have hsum2 : ∑ i : Fin n, (-(p i * Real.log (p i)) - p i * Real.log n)
      ≤ ∑ i : Fin n, (1 / (n : ℝ) - p i) := Finset.sum_le_sum fun i _ => key i
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum] at hsum2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    one_mul] at hsum2
  have hnn : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
  have h3 : ∑ i : Fin n, -(p i * Real.log (p i)) = -∑ i : Fin n, p i * Real.log (p i) := by simp
  unfold shannonEntropy
  rw [h3]
  linarith [hsum2, hnn]

/-- No single bit carries more than `log 2` nats of entropy, so `k * T * log 2` is exactly
the largest heat that Landauer's bound can demand for the erasure of one bit. -/
