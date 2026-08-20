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


theorem almostDecisive_split (hF : IsSWF F) (hI : IIA F)
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {S : Finset V} {i : V} (hi : i ∈ S)
    (hS : ∀ u v : A, u ≠ v → Decisive F S u v) :
    AlmostDecisive F {i} a c ∨ AlmostDecisive F (S.erase i) c b := by
  classical
  obtain ⟨base, hbase⟩ := exists_ranking A
  set pr : V → A → ℕ := fun j w =>
    if j = i then (if w = a then 0 else if w = b then 1 else if w = c then 2 else 3)
    else if j ∈ S then (if w = c then 0 else if w = a then 1 else if w = b then 2 else 3)
    else (if w = b then 0 else if w = c then 1 else if w = a then 2 else 3) with hpr
  set q : V → A → A → Prop := fun j => lexRel base (pr j) with hq
  have hqprof : IsProfile q := fun j => isRanking_lexRel hbase _
  -- the values of `pr`
  have hia : pr i a = 0 := by simp [hpr]
  have hib : pr i b = 1 := by simp [hpr, hab.symm]
  have hic : pr i c = 2 := by simp [hpr, hac.symm, hbc.symm]
  have hSa : ∀ j, j ∈ S → j ≠ i → pr j a = 1 := by intro j hj hji; simp [hpr, hj, hji, hac]
  have hSb : ∀ j, j ∈ S → j ≠ i → pr j b = 2 := by
    intro j hj hji; simp [hpr, hj, hji, hbc, hab.symm]
  have hSc : ∀ j, j ∈ S → j ≠ i → pr j c = 0 := by intro j hj hji; simp [hpr, hj, hji]
  have hNa : ∀ j, j ∉ S → pr j a = 2 := by
    intro j hj
    have hji : j ≠ i := by rintro rfl; exact hj hi
    simp [hpr, hj, hji, hab, hac]
  have hNb : ∀ j, j ∉ S → pr j b = 0 := by
    intro j hj
    have hji : j ≠ i := by rintro rfl; exact hj hi
    simp [hpr, hj, hji]
  have hNc : ∀ j, j ∉ S → pr j c = 1 := by
    intro j hj
    have hji : j ≠ i := by rintro rfl; exact hj hi
    simp [hpr, hj, hji, hbc.symm]
  -- society prefers `a` to `b`
  have hab_soc : F q a b := by
    refine hS a b hab q hqprof (fun j hj => lexRel_of_lt ?_)
    by_cases hji : j = i
    · subst hji; rw [hia, hib]; omega
    · rw [hSa j hj hji, hSb j hj hji]; omega
  by_cases hac_soc : F q a c
  · -- `{i}` is almost decisive for `(a, c)`
    left
    intro p hp hpS hpN
    refine (hI p q hp hqprof a c ?_).mpr hac_soc
    intro j
    by_cases hji : j = i
    · subst hji
      exact iff_pair (hp j) (hqprof j) (hpS j (Finset.mem_singleton_self j))
        (lexRel_of_lt (by rw [hia, hic]; omega))
    · have hjn : j ∉ ({i} : Finset V) := by simpa using hji
      refine iff_pair_swap (hp j) (hqprof j) (hpN j hjn) (lexRel_of_lt ?_)
      by_cases hjS : j ∈ S
      · rw [hSa j hjS hji, hSc j hjS hji]; omega
      · rw [hNa j hjS, hNc j hjS]; omega
  · -- otherwise `S \ {i}` is almost decisive for `(c, b)`
    right
    have hca_soc : F q c a := (hF q hqprof).of_not hac hac_soc
    have hcb_soc : F q c b := (hF q hqprof).trans hca_soc hab_soc
    intro p hp hpS hpN
    refine (hI p q hp hqprof c b ?_).mpr hcb_soc
    intro j
    by_cases hjm : j ∈ S.erase i
    · have hji : j ≠ i := Finset.ne_of_mem_erase hjm
      have hjS : j ∈ S := Finset.mem_of_mem_erase hjm
      exact iff_pair (hp j) (hqprof j) (hpS j hjm)
        (lexRel_of_lt (by rw [hSc j hjS hji, hSb j hjS hji]; omega))
    · refine iff_pair_swap (hp j) (hqprof j) (hpN j hjm) (lexRel_of_lt ?_)
      by_cases hji : j = i
      · subst hji; rw [hib, hic]; omega
      · have hjS : j ∉ S := fun hjS => hjm (Finset.mem_erase.mpr ⟨hji, hjS⟩)
        rw [hNb j hjS, hNc j hjS]; omega

/-- Every nonempty decisive coalition contains a decisive singleton. -/
