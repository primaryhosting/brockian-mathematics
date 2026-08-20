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

theorem Psi_le_const {q r : ℝ} (hq : 0 < q) (hr : 64 * q ≤ r) (hr1 : r ≤ 1) (b : ℕ)
    (H : Finset (Finset α)) (hH : ∀ S ∈ H, S.card ≤ b) : Psi r q H b ≤ 8 * q / r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hr
  have hy0 : 0 ≤ 4 * q / r := by positivity
  have hy : 4 * q / r ≤ 1 / 2 := by
    rw [div_le_iff₀ hr0]
    linarith
  have h1 : ∑ m ∈ Finset.range b, (4 * q / r) ^ (m + 1)
      = (4 * q / r) * ∑ m ∈ Finset.range b, (4 * q / r) ^ m := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [pow_succ]; ring
  have h2 : ∑ m ∈ Finset.range b, (4 * q / r) ^ m ≤ 2 := geom_sum_two_bound hy0 hy b
  have h3 : ∑ m ∈ Finset.range b, (4 * q / r) ^ (m + 1) ≤ 8 * q / r := by
    rw [h1]
    calc (4 * q / r) * ∑ m ∈ Finset.range b, (4 * q / r) ^ m
        ≤ (4 * q / r) * 2 := mul_le_mul_of_nonneg_left h2 hy0
      _ = 8 * q / r := by ring
  exact le_trans (Psi_le hq hr hr1 b H hH) h3

end Math2

/-
The key lemma of Park–Pham: the cover produced at one step of the iteration has small
expected cost.
-/
import Mathlib
import RequestProject.KahnKalai.Cover

open Finset
open scoped Classical

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A canonical edge of `H` contained in `Z` (or `∅` if there is none). -/
