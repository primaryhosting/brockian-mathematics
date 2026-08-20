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

lemma Fail_step {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (H : Finset (Finset α)) (n : ℕ) :
    Fail (pp r (n + 1)) H
      ≤ ∑ W : Finset α, nu r W * Fail (pp r ((n + 1) / 2)) (Hnext H ((n + 1) / 2) W) := by
  classical
  set b' := (n + 1) / 2 with hb'
  set s := pp r b' with hs
  have hs0 : 0 ≤ s := pp_nonneg hr0 hr1 b'
  have hs1 : s ≤ 1 := pp_le_one hr0 hr1 b'
  have hrew : Fail (pp r (n + 1)) H
      = ∑ W : Finset α, ∑ V : Finset α,
          nu r W * nu s V * (if ∃ S ∈ H, S ⊆ W ∪ V then 0 else 1) := by
    rw [pp_succ, Fail, ← hs]
    exact (sum_nu_union r s (fun U => if ∃ S ∈ H, S ⊆ U then 0 else 1)).symm
  rw [hrew]
  refine Finset.sum_le_sum fun W _ => ?_
  rw [Fail, Finset.mul_sum]
  refine Finset.sum_le_sum fun V _ => ?_
  have hnu : 0 ≤ nu r W * nu s V := mul_nonneg (nu_nonneg hr0 hr1 W) (nu_nonneg hs0 hs1 V)
  have hind : (if ∃ S ∈ H, S ⊆ W ∪ V then (0:ℝ) else 1)
      ≤ (if ∃ T ∈ Hnext H b' W, T ⊆ V then (0:ℝ) else 1) := by
    by_cases hT : ∃ T ∈ Hnext H b' W, T ⊆ V
    · obtain ⟨T, hTmem, hTV⟩ := hT
      obtain ⟨S', hS', hS'sub⟩ := Hnext_capture H b' W T hTmem
      have : ∃ S ∈ H, S ⊆ W ∪ V := by
        refine ⟨S', hS', hS'sub.trans ?_⟩
        exact Finset.union_subset_union_right hTV
      simp only [this, if_true]
      split <;> norm_num
    · simp [hT]
      split <;> norm_num
  calc nu r W * nu s V * (if ∃ S ∈ H, S ⊆ W ∪ V then (0:ℝ) else 1)
      ≤ nu r W * nu s V * (if ∃ T ∈ Hnext H b' W, T ⊆ V then (0:ℝ) else 1) :=
        mul_le_mul_of_nonneg_left hind hnu
    _ = nu r W * (nu s V * (if ∃ T ∈ Hnext H b' W, T ⊆ V then (0:ℝ) else 1)) := by ring

/-- **The main induction.** For a `b`-bounded hypergraph `H`, the failure probability after
`rounds b` rounds, weighted by the minimal cover cost, is at most `Psi`. -/
