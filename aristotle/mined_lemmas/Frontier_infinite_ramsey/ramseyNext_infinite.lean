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

namespace Frontier

variable (c : ℕ → ℕ → Bool)

open Classical in
/-- The colour chosen at a stage of the Ramsey construction: `true` if the set of elements of
`S` above `sInf S` that are joined to `sInf S` in colour `true` is infinite, `false` otherwise. -/

lemma ramseyNext_infinite {S : Set ℕ} (hS : S.Infinite) : (ramseyNext c S).Infinite := by
  classical
  by_cases h : {x ∈ S | sInf S < x ∧ c (sInf S) x = true}.Infinite
  · have hc : ramseyColor c S = true := by unfold ramseyColor; rw [if_pos h]
    simpa [ramseyNext, hc] using h
  · have hc : ramseyColor c S = false := by unfold ramseyColor; rw [if_neg h]
    have hbig := infinite_gt_sInf hS
    have hsub : {x ∈ S | sInf S < x} ⊆
        {x ∈ S | sInf S < x ∧ c (sInf S) x = true} ∪
          {x ∈ S | sInf S < x ∧ c (sInf S) x = false} := by
      rintro x ⟨hxS, hx⟩
      rcases Bool.eq_false_or_eq_true (c (sInf S) x) with hcx | hcx
      · exact Or.inl ⟨hxS, hx, hcx⟩
      · exact Or.inr ⟨hxS, hx, hcx⟩
    have hunion : ({x ∈ S | sInf S < x ∧ c (sInf S) x = true} ∪
        {x ∈ S | sInf S < x ∧ c (sInf S) x = false}).Infinite := hbig.mono hsub
    have hfalse : {x ∈ S | sInf S < x ∧ c (sInf S) x = false}.Infinite := by
      intro hfin
      exact hunion ((Set.not_infinite.mp h).union hfin)
    simpa [ramseyNext, hc] using hfalse

