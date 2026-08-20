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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Brockian.Equidistribution

/-- Triangular numbers: `T m = 1 + 2 + ⋯ + m = m (m+1) / 2`. -/

lemma abs_Cnt_div_sub_le (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (N : ℕ)
    (hN : 1 ≤ blk N) :
    |(Cnt a b N : ℝ) / N - (b - a)| ≤ 6 / ((blk N : ℝ) + 1) := by
  set M := blk N with hMdef
  have hTM : T M ≤ N := T_blk_le N
  have hNlt : N < T (M + 1) := lt_T_blk_succ N
  have hTsucc : T (M + 1) = T M + (M + 1) := T_succ M
  obtain ⟨r, hr⟩ : ∃ r, N = T M + r := ⟨N - T M, by omega⟩
  have hrM : r ≤ M := by omega
  have hCT := Cnt_T a b ha hab hb M
  have hup : Cnt a b N ≤ Cnt a b (T M) + r := by rw [hr]; exact Cnt_le_add a b (T M) r
  have hlow : Cnt a b (T M) ≤ Cnt a b N := by rw [hr]; exact Cnt_mono_add a b (T M) r
  have hT1 : T 1 ≤ T M := T_mono hN
  have hTMpos : 0 < T M := by
    have : T 1 = 1 := by simp [T]
    omega
  have hNpos : (0:ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hupR : (Cnt a b N : ℝ) ≤ (Cnt a b (T M) : ℝ) + (r : ℝ) := by exact_mod_cast hup
  have hlowR : (Cnt a b (T M) : ℝ) ≤ (Cnt a b N : ℝ) := by exact_mod_cast hlow
  have hNR : (N : ℝ) = (T M : ℝ) + (r : ℝ) := by exact_mod_cast hr
  have h2TR : 2 * (T M : ℝ) = (M : ℝ) * ((M : ℝ) + 1) := by
    have := two_mul_T M
    exact_mod_cast this
  have hrMR : (r : ℝ) ≤ (M : ℝ) := by exact_mod_cast hrM
  have hr0 : (0:ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have hba0 : (0:ℝ) ≤ b - a := by linarith
  have hba1 : b - a ≤ 1 := by linarith
  have hCTabs := abs_le.mp hCT
  have hkey : |(Cnt a b N : ℝ) - (b - a) * (N : ℝ)| ≤ 3 * (M : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith [hCTabs.1, hCTabs.2]
  have hM1pos : (0:ℝ) < (M : ℝ) + 1 := by positivity
  have hsplit : (Cnt a b N : ℝ) / (N : ℝ) - (b - a)
      = ((Cnt a b N : ℝ) - (b - a) * (N : ℝ)) / (N : ℝ) := by
    field_simp
  rw [hsplit, abs_div, abs_of_pos hNpos, div_le_div_iff₀ hNpos hM1pos]
  have hTMR : (T M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hTM
  nlinarith [hkey, hM1pos, hTMR, h2TR]

