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

lemma per_size_bound {H : Finset (Finset α)} {l : ℕ} (hH : ∀ S ∈ H, S.card ≤ l)
    {q r : ℝ} (hq : 0 ≤ q) (hr0 : 0 < r) (hr1 : r ≤ 1) (b m : ℕ) :
    ∑ W : Finset α, nu r W * ((((Ucov H b W).filter (fun U => U.card = m)).card : ℝ) * q ^ m)
      ≤ 2 ^ l * (q / r) ^ m := by
  classical
  have hkey : ∀ W : Finset α,
      nu r W * ((((Ucov H b W).filter (fun U => U.card = m)).card : ℝ) * q ^ m)
        ≤ (q ^ m * (1 / r) ^ m) *
            ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U) := by
    intro W
    have hexp : ∀ U ∈ (Ucov H b W).filter (fun U => U.card = m),
        nu r W = nu r (W ∪ U) * ((1 - r) / r) ^ m := by
      intro U hU
      rw [Finset.mem_filter] at hU
      obtain ⟨S, hS, hSe⟩ := Finset.mem_image.mp hU.1
      have hd : Disjoint W U := by
        rw [← hSe]; exact frag_disjoint (Finset.mem_filter.mp hS).1 W
      rw [nu_split hr0 hd, hU.2]
    have hsum : nu r W * (((Ucov H b W).filter (fun U => U.card = m)).card : ℝ)
        = ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U) * ((1 - r) / r) ^ m := by
      rw [← Finset.sum_congr rfl hexp, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hrle : ((1 - r) / r) ^ m ≤ (1 / r) ^ m := by
      gcongr
      · exact div_nonneg (by linarith) hr0.le
      · linarith
    calc nu r W * ((((Ucov H b W).filter (fun U => U.card = m)).card : ℝ) * q ^ m)
        = (nu r W * (((Ucov H b W).filter (fun U => U.card = m)).card : ℝ)) * q ^ m := by ring
      _ = (∑ U ∈ (Ucov H b W).filter (fun U => U.card = m),
            nu r (W ∪ U) * ((1 - r) / r) ^ m) * q ^ m := by rw [hsum]
      _ ≤ (∑ U ∈ (Ucov H b W).filter (fun U => U.card = m),
            nu r (W ∪ U) * (1 / r) ^ m) * q ^ m := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hq m)
          refine Finset.sum_le_sum fun U _ => ?_
          exact mul_le_mul_of_nonneg_left hrle (nu_nonneg (le_of_lt hr0) hr1 _)
      _ = (q ^ m * (1 / r) ^ m) *
            ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U) := by
          rw [← Finset.sum_mul]; ring
  calc ∑ W : Finset α, nu r W * ((((Ucov H b W).filter (fun U => U.card = m)).card : ℝ) * q ^ m)
      ≤ ∑ W : Finset α, (q ^ m * (1 / r) ^ m) *
          ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U) :=
        Finset.sum_le_sum fun W _ => hkey W
    _ = (q ^ m * (1 / r) ^ m) * ∑ W : Finset α,
          ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U) := by
        rw [← Finset.mul_sum]
    _ ≤ (q ^ m * (1 / r) ^ m) * 2 ^ l := by
        refine mul_le_mul_of_nonneg_left (double_sum_bound hH (le_of_lt hr0) hr1 b m) ?_
        positivity
    _ = 2 ^ l * (q / r) ^ m := by
        rw [div_pow, div_pow]; ring

/-- **Key lemma** (Park–Pham). The expected cost of the cover produced at one step of the
iteration is small. -/
