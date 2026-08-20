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
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Rankings (strict total orders) -/

/-- A *ranking* of the alternatives `A` is a strict total order: an irreflexive,
transitive and total (trichotomous) relation.  `r x y` means "`x` is strictly
preferred to `y`". -/
structure IsRanking {A : Type*} (r : A → A → Prop) : Prop where
  irrefl : ∀ x, ¬ r x x
  trans : ∀ {x y z}, r x y → r y z → r x z
  total : ∀ x y, x ≠ y → r x y ∨ r y x

namespace IsRanking

variable {A : Type*} {r : A → A → Prop}


theorem decisive_snd_of_almostDecisive (hF : IsSWF F) (hU : Unanimity F) (hI : IIA F)
    {S : Finset V} {x y z : A} (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (h : AlmostDecisive F S x y) : Decisive F S z y := by
  classical
  intro p hp hpS
  obtain ⟨base, hbase⟩ := exists_ranking A
  set pr : V → A → ℕ := fun j w =>
    if j ∈ S then (if w = z then 0 else if w = x then 1 else if w = y then 2 else 3)
    else (if w = x then 2 else if w = z then (if p j z y then 0 else 1)
          else if w = y then (if p j z y then 1 else 0) else 3) with hpr
  set q : V → A → A → Prop := fun j => lexRel base (pr j) with hq
  have hqprof : IsProfile q := fun j => isRanking_lexRel hbase _
  have hprz : ∀ j, j ∈ S → pr j z = 0 := by intro j hj; simp [hpr, hj]
  have hprx : ∀ j, j ∈ S → pr j x = 1 := by intro j hj; simp [hpr, hj, hzx.symm]
  have hpry : ∀ j, j ∈ S → pr j y = 2 := by intro j hj; simp [hpr, hj, hzy.symm, hxy.symm]
  have hprx' : ∀ j, j ∉ S → pr j x = 2 := by intro j hj; simp [hpr, hj]
  have hprz' : ∀ j, j ∉ S → pr j z = (if p j z y then 0 else 1) := by
    intro j hj; simp [hpr, hj, hzx]
  have hpry' : ∀ j, j ∉ S → pr j y = (if p j z y then 1 else 0) := by
    intro j hj; simp [hpr, hj, hxy.symm, hzy.symm]
  -- everybody prefers z to x
  have hzx_soc : F q z x := by
    refine hU q hqprof z x (fun i => lexRel_of_lt ?_)
    by_cases hi : i ∈ S
    · rw [hprz i hi, hprx i hi]; omega
    · rw [hprz' i hi, hprx' i hi]; split <;> omega
  -- society prefers x to y
  have hxy_soc : F q x y := by
    refine h q hqprof (fun i hi => lexRel_of_lt ?_) (fun i hi => lexRel_of_lt ?_)
    · rw [hprx i hi, hpry i hi]; omega
    · rw [hpry' i hi, hprx' i hi]; split <;> omega
  have hzy_soc : F q z y := (hF q hqprof).trans hzx_soc hxy_soc
  have hiia := hI p q hp hqprof z y ?_
  · exact hiia.mpr hzy_soc
  · intro j
    by_cases hj : j ∈ S
    · have h1 : p j z y := hpS j hj
      have h2 : q j z y := lexRel_of_lt (by rw [hprz j hj, hpry j hj]; omega)
      exact ⟨by simp [h1, h2], by simp [(hp j).asymm h1, (hqprof j).asymm h2]⟩
    · by_cases hpz : p j z y
      · have h2 : q j z y := lexRel_of_lt (by
          rw [hprz' j hj, hpry' j hj, if_pos hpz, if_pos hpz]; omega)
        exact ⟨by simp [hpz, h2], by simp [(hp j).asymm hpz, (hqprof j).asymm h2]⟩
      · have h1 : p j y z := (hp j).of_not hzy hpz
        have h2 : q j y z := lexRel_of_lt (by
          rw [hprz' j hj, hpry' j hj, if_neg hpz, if_neg hpz]; omega)
        exact ⟨by simp [hpz, (hqprof j).asymm h2], by simp [h1, h2]⟩

/-- Pigeonhole: among three distinct alternatives one avoids any two given distinct ones. -/
