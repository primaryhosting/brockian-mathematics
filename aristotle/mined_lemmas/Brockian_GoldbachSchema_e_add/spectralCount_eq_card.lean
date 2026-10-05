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

/-
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.GoldbachSchema

noncomputable section

/-- The additive character `e(x) = exp(2πi x)` on the circle. -/

theorem spectralCount_eq_card (n : ℕ) : spectralCount n = ((reps n).card : ℂ) := by
  set P := (Finset.range (n + 1)).filter Nat.Prime with hP
  have hNR : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hNC : ((n : ℂ) + 1) ≠ 0 := by
    have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have step1 : ∀ k ∈ Finset.range (n + 1),
      (primeExpSum n ((k : ℝ) / (n + 1))) ^ 2 * e (((-(n : ℤ) * k : ℤ) : ℝ) / (n + 1 : ℝ))
        = ∑ pq ∈ P ×ˢ P, e (((((pq.1 : ℤ) + (pq.2 : ℤ) - n) * k : ℤ) : ℝ) / (n + 1 : ℝ)) := by
    intro k _
    rw [primeExpSum_sq, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun pq _ => ?_)
    rw [← e_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [spectralCount, Finset.sum_congr rfl step1, Finset.sum_comm]
  have step2 : ∀ pq ∈ P ×ˢ P,
      ∑ k ∈ Finset.range (n + 1), e (((((pq.1 : ℤ) + (pq.2 : ℤ) - n) * k : ℤ) : ℝ) / (n + 1 : ℝ))
        = if pq.1 + pq.2 = n then ((n : ℂ) + 1) else 0 := by
    intro pq hpq
    have h := sum_e_orthogonality (n + 1) (Nat.succ_pos n) (((pq.1 : ℤ) + (pq.2 : ℤ) - n))
    push_cast at h ⊢
    rw [h]
    simp only [Finset.mem_product, hP, Finset.mem_filter, Finset.mem_range] at hpq
    by_cases hs : pq.1 + pq.2 = n
    · rw [if_pos (by simp [show ((pq.1 : ℤ) + pq.2 - n) = 0 by omega]), if_pos hs]
    · rw [if_neg ?_, if_neg hs]
      intro hdvd
      have habs : ((pq.1 : ℤ) + (pq.2 : ℤ) - n) = 0 := by
        obtain ⟨c, hc⟩ := hdvd
        have h1 : ((pq.1 : ℤ) + pq.2) - n ≤ n := by omega
        have h2 : -(n : ℤ) ≤ ((pq.1 : ℤ) + pq.2) - n := by omega
        have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg _
        rcases lt_trichotomy c 0 with hc1 | hc1 | hc1
        · have hle : ((n : ℤ) + 1) * c ≤ ((n : ℤ) + 1) * (-1) :=
            mul_le_mul_of_nonneg_left (by omega) (by linarith)
          linarith
        · simp [hc1] at hc; linarith
        · have hle : ((n : ℤ) + 1) * 1 ≤ ((n : ℤ) + 1) * c :=
            mul_le_mul_of_nonneg_left (by omega) (by linarith)
          linarith
      omega
  rw [Finset.sum_congr rfl step2, ← Finset.sum_filter, Finset.sum_const]
  have hfilter : (P ×ˢ P).filter (fun pq => pq.1 + pq.2 = n) = reps n := by
    ext pq
    simp only [reps, hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    tauto
  rw [hfilter]
  field_simp
  ring

/-- The spectral model hypothesis: the spectral count of every even `n ≥ 4` is positive. -/
