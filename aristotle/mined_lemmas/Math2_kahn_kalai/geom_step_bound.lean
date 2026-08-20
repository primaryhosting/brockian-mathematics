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
Covers, costs, and minimum fragments (Park–Pham).
-/
import Mathlib
import RequestProject.KahnKalai.Measure

open Finset
open scoped Classical

namespace Math2

variable {α : Type*} [DecidableEq α]

/-! ## Covers and their costs -/

/-- `G` is a cover of `H`: every member of `H` contains a member of `G`. -/

lemma geom_step_bound {q r : ℝ} (hq : 0 < q) (hr : 64 * q ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    (2 : ℝ) ^ (n + 1) * ∑ m ∈ Finset.Ico ((n + 1) / 2 + 1) (n + 2), (q / r) ^ m
      ≤ (4 * q / r) ^ ((n + 1) / 2 + 1) := by
  set b' := (n + 1) / 2 with hb'
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hr
  set ρ : ℝ := q / r with hρ
  have hρ0 : 0 < ρ := div_pos hq hr0
  have hρle : ρ ≤ 1 / 64 := by
    rw [hρ, div_le_iff₀ hr0]
    linarith
  have hsum : ∑ m ∈ Finset.Ico (b' + 1) (n + 2), ρ ^ m
      = ρ ^ (b' + 1) * ∑ j ∈ Finset.range (n + 2 - (b' + 1)), ρ ^ j := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_add]
  have hgeom : ∑ j ∈ Finset.range (n + 2 - (b' + 1)), ρ ^ j ≤ 2 :=
    geom_sum_two_bound hρ0.le (by linarith) _
  have hpow : (2 : ℝ) ^ (n + 1) * 2 ≤ 4 ^ (b' + 1) := by
    have h4 : (4 : ℝ) ^ (b' + 1) = 2 ^ (2 * (b' + 1)) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [h4, show (2 : ℝ) ^ (n + 1) * 2 = 2 ^ (n + 2) by ring]
    refine pow_le_pow_right₀ (by norm_num) ?_
    omega
  have hfinal : (4 * q / r) ^ (b' + 1) = 4 ^ (b' + 1) * ρ ^ (b' + 1) := by
    rw [hρ, ← mul_pow]
    congr 1
    field_simp
  rw [hsum, hfinal]
  have hpos : (0 : ℝ) < ρ ^ (b' + 1) := pow_pos hρ0 _
  calc (2 : ℝ) ^ (n + 1) * (ρ ^ (b' + 1) * ∑ j ∈ Finset.range (n + 2 - (b' + 1)), ρ ^ j)
      ≤ (2 : ℝ) ^ (n + 1) * (ρ ^ (b' + 1) * 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hgeom hpos.le
    _ = ((2 : ℝ) ^ (n + 1) * 2) * ρ ^ (b' + 1) := by ring
    _ ≤ 4 ^ (b' + 1) * ρ ^ (b' + 1) := mul_le_mul_of_nonneg_right hpow hpos.le

/-- **The bound on `Psi`.** -/
