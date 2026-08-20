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


theorem decisive_fst_of_almostDecisive (hF : IsSWF F) (hU : Unanimity F) (hI : IIA F)
    {S : Finset V} {x y z : A} (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (h : AlmostDecisive F S x y) : Decisive F S x z := by
  classical
  intro p hp hpS
  obtain ⟨base, hbase⟩ := exists_ranking A
  set pr : V → A → ℕ := fun j w =>
    if j ∈ S then (if w = x then 0 else if w = y then 1 else if w = z then 2 else 3)
    else (if w = y then 0 else if w = x then (if p j x z then 1 else 2)
          else if w = z then (if p j x z then 2 else 1) else 3) with hpr
  set q : V → A → A → Prop := fun j => lexRel base (pr j) with hq
  have hqprof : IsProfile q := fun j => isRanking_lexRel hbase _
  -- values of `pr`
  have hprx : ∀ j, j ∈ S → pr j x = 0 := by intro j hj; simp [hpr, hj]
  have hpry : ∀ j, j ∈ S → pr j y = 1 := by intro j hj; simp [hpr, hj, hxy.symm]
  have hprz : ∀ j, j ∈ S → pr j z = 2 := by intro j hj; simp [hpr, hj, hzx, hzy]
  have hpry' : ∀ j, j ∉ S → pr j y = 0 := by intro j hj; simp [hpr, hj]
  have hprx' : ∀ j, j ∉ S → pr j x = (if p j x z then 1 else 2) := by
    intro j hj; simp [hpr, hj, hxy]
  have hprz' : ∀ j, j ∉ S → pr j z = (if p j x z then 2 else 1) := by
    intro j hj; simp [hpr, hj, hzx, hzy]
  -- society prefers x to y
  have hxy_soc : F q x y := by
    refine h q hqprof (fun i hi => lexRel_of_lt ?_) (fun i hi => lexRel_of_lt ?_)
    · rw [hprx i hi, hpry i hi]; omega
    · rw [hpry' i hi, hprx' i hi]; split <;> omega
  -- everybody prefers y to z
  have hyz_soc : F q y z := by
    refine hU q hqprof y z (fun i => lexRel_of_lt ?_)
    by_cases hi : i ∈ S
    · rw [hpry i hi, hprz i hi]; omega
    · rw [hpry' i hi, hprz' i hi]; split <;> omega
  have hxz_soc : F q x z := (hF q hqprof).trans hxy_soc hyz_soc
  -- transfer to `p` by IIA
  have hiia := hI p q hp hqprof x z ?_
  · exact hiia.mpr hxz_soc
  · intro j
    by_cases hj : j ∈ S
    · have h1 : p j x z := hpS j hj
      have h2 : q j x z := lexRel_of_lt (by rw [hprx j hj, hprz j hj]; omega)
      exact ⟨by simp [h1, h2], by
        simp [(hp j).asymm h1, (hqprof j).asymm h2]⟩
    · by_cases hpz : p j x z
      · have h2 : q j x z := lexRel_of_lt (by
          rw [hprx' j hj, hprz' j hj, if_pos hpz, if_pos hpz]; omega)
        exact ⟨by simp [hpz, h2], by
          simp [(hp j).asymm hpz, (hqprof j).asymm h2]⟩
      · have h1 : p j z x := (hp j).of_not (Ne.symm hzx) hpz
        have h2 : q j z x := lexRel_of_lt (by
          rw [hprx' j hj, hprz' j hj, if_neg hpz, if_neg hpz]; omega)
        exact ⟨by simp [hpz, (hqprof j).asymm h2], by simp [h1, h2]⟩

/-- From almost-decisiveness over `(x, y)` we get full decisiveness over `(z, y)`. -/
