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

theorem asymm (h : IsRanking r) {x y : A} (hxy : r x y) : ¬ r y x := fun hyx =>
  h.irrefl x (h.trans hxy hyx)

theorem of_not (h : IsRanking r) {x y : A} (hne : x ≠ y) (hn : ¬ r x y) : r y x :=
  (h.total x y hne).resolve_left hn

end IsRanking

/-! ## A generic way of building rankings -/

/-- Rank alternatives by a numerical priority `pr`, breaking ties with a base ranking. -/
def lexRel {A : Type*} (base : A → A → Prop) (pr : A → ℕ) : A → A → Prop :=
  fun x y => pr x < pr y ∨ (pr x = pr y ∧ base x y)

theorem lexRel_of_lt {A : Type*} {base : A → A → Prop} {pr : A → ℕ} {x y : A}
    (h : pr x < pr y) : lexRel base pr x y := Or.inl h

theorem isRanking_lexRel {A : Type*} {base : A → A → Prop} (hb : IsRanking base)
    (pr : A → ℕ) : IsRanking (lexRel base pr) where
  irrefl x := by
    rintro (h | ⟨-, h⟩)
    · exact lt_irrefl _ h
    · exact hb.irrefl x h
  trans := by
    rintro x y z (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (h2 ▸ h1)
    · exact Or.inl (h1 ▸ h2)
    · exact Or.inr ⟨h1.trans h2, hb.trans h1' h2'⟩
  total x y hne := by
    rcases lt_trichotomy (pr x) (pr y) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases hb.total x y hne with hb' | hb'
      · exact Or.inl (Or.inr ⟨h, hb'⟩)
      · exact Or.inr (Or.inr ⟨h.symm, hb'⟩)
    · exact Or.inr (Or.inl h)

theorem exists_ranking (A : Type*) : ∃ r : A → A → Prop, IsRanking r := by
  refine ⟨WellOrderingRel, ?_, ?_, ?_⟩
  · exact fun x => irrefl_of WellOrderingRel x
  · exact fun {x y z} => trans_of WellOrderingRel
  · intro x y h
    rcases trichotomous_of WellOrderingRel x y with h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd h1 h
    · exact Or.inr h1

/-! ## Social welfare functions -/

variable {V A : Type*}

/-- A *profile* assigns a ranking of the alternatives to every voter. -/
def IsProfile (p : V → A → A → Prop) : Prop := ∀ i, IsRanking (p i)

/-- A social welfare function turns profiles into rankings. -/
def IsSWF (F : (V → A → A → Prop) → (A → A → Prop)) : Prop :=
  ∀ p, IsProfile p → IsRanking (F p)

/-- Unanimity (the weak Pareto property). -/
def Unanimity (F : (V → A → A → Prop) → (A → A → Prop)) : Prop :=
  ∀ p, IsProfile p → ∀ x y, (∀ i, p i x y) → F p x y

/-- Independence of irrelevant alternatives. -/
def IIA (F : (V → A → A → Prop) → (A → A → Prop)) : Prop :=
  ∀ p q, IsProfile p → IsProfile q → ∀ x y,
    (∀ i, (p i x y ↔ q i x y) ∧ (p i y x ↔ q i y x)) → (F p x y ↔ F q x y)

/-- Voter `i` is a dictator: society always follows `i`'s strict preferences. -/
def IsDictator (F : (V → A → A → Prop) → (A → A → Prop)) (i : V) : Prop :=
  ∀ p, IsProfile p → ∀ x y, p i x y → F p x y

/-- A coalition `S` is *decisive* for the ordered pair `(x, y)` if society ranks
`x` above `y` whenever all members of `S` do. -/
def Decisive (F : (V → A → A → Prop) → (A → A → Prop)) (S : Finset V) (x y : A) : Prop :=
  ∀ p, IsProfile p → (∀ i ∈ S, p i x y) → F p x y

/-- A coalition `S` is *almost decisive* for `(x, y)` if society ranks `x` above `y`
whenever all members of `S` do and all non-members rank `y` above `x`. -/
def AlmostDecisive (F : (V → A → A → Prop) → (A → A → Prop)) (S : Finset V) (x y : A) : Prop :=
  ∀ p, IsProfile p → (∀ i ∈ S, p i x y) → (∀ i ∉ S, p i y x) → F p x y

theorem AlmostDecisive.of_decisive {F : (V → A → A → Prop) → (A → A → Prop)}
    {S : Finset V} {x y : A} (h : Decisive F S x y) : AlmostDecisive F S x y :=
  fun p hp hS _ => h p hp hS

/-! ## Field expansion -/

section FieldExpansion

variable {F : (V → A → A → Prop) → (A → A → Prop)}

/-- From almost-decisiveness over `(x, y)` we get full decisiveness over `(x, z)`. -/
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
theorem exists_avoiding {x y t : A} (hxy : x ≠ y) (hxt : x ≠ t) (hyt : y ≠ t)
    (u v : A) :
    (x ≠ u ∧ x ≠ v) ∨ (y ≠ u ∧ y ≠ v) ∨ (t ≠ u ∧ t ≠ v) := by
  grind

/-- **Field expansion**: a coalition that is almost decisive for a single ordered pair is
decisive for every ordered pair (given at least three alternatives). -/
theorem decisive_all_of_almostDecisive (hF : IsSWF F) (hU : Unanimity F) (hI : IIA F)
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {S : Finset V} {x y : A} (hxy : x ≠ y) (h : AlmostDecisive F S x y) :
    ∀ u v : A, u ≠ v → Decisive F S u v := by
  classical
  -- pick a third alternative `t` distinct from `x` and `y`
  obtain ⟨t, htx, hty⟩ : ∃ t : A, t ≠ x ∧ t ≠ y := by
    rcases exists_avoiding hab hac hbc x y with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a, h1, h2⟩
    · exact ⟨b, h1, h2⟩
    · exact ⟨c, h1, h2⟩
  -- all six ordered pairs from {x, y, t}
  have hxt : Decisive F S x t :=
    decisive_fst_of_almostDecisive hF hU hI hxy htx hty h
  have hDty : Decisive F S t y :=
    decisive_snd_of_almostDecisive hF hU hI hxy htx hty h
  have hyt : Decisive F S y t :=
    decisive_snd_of_almostDecisive hF hU hI (Ne.symm htx) (Ne.symm hxy) (Ne.symm hty)
      (AlmostDecisive.of_decisive hxt)
  have hyx : Decisive F S y x :=
    decisive_fst_of_almostDecisive hF hU hI (Ne.symm hty) hxy (Ne.symm htx)
      (AlmostDecisive.of_decisive hyt)
  have htx' : Decisive F S t x :=
    decisive_fst_of_almostDecisive hF hU hI hty (Ne.symm htx) hxy
      (AlmostDecisive.of_decisive hDty)
  have hxy' : Decisive F S x y :=
    decisive_snd_of_almostDecisive hF hU hI hty (Ne.symm htx) hxy
      (AlmostDecisive.of_decisive hDty)
  -- almost decisiveness for all ordered pairs from {x, y, t}
  have key : ∀ u v : A, (u = x ∨ u = y ∨ u = t) → (v = x ∨ v = y ∨ v = t) → u ≠ v →
      AlmostDecisive F S u v := by
    rintro u v (rfl | rfl | rfl) (rfl | rfl | rfl) hne
    · exact absurd rfl hne
    · exact AlmostDecisive.of_decisive hxy'
    · exact AlmostDecisive.of_decisive hxt
    · exact AlmostDecisive.of_decisive hyx
    · exact absurd rfl hne
    · exact AlmostDecisive.of_decisive hyt
    · exact AlmostDecisive.of_decisive htx'
    · exact AlmostDecisive.of_decisive hDty
    · exact absurd rfl hne
  intro u v huv
  -- pick a member `w` of {x, y, t} different from `u` and `v`
  obtain ⟨w, hw, hwu, hwv⟩ : ∃ w : A, (w = x ∨ w = y ∨ w = t) ∧ w ≠ u ∧ w ≠ v := by
    rcases exists_avoiding hxy (Ne.symm htx) (Ne.symm hty) u v with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨x, Or.inl rfl, h1, h2⟩
    · exact ⟨y, Or.inr (Or.inl rfl), h1, h2⟩
    · exact ⟨t, Or.inr (Or.inr rfl), h1, h2⟩
  -- first show `S` is almost decisive for `(u, w)`
  have huw : AlmostDecisive F S u w := by
    by_cases hu : u = x ∨ u = y ∨ u = t
    · exact key u w hu hw (Ne.symm hwu)
    · -- `u` is outside {x, y, t}; pick some pair from {x, y, t} avoiding `u`
      push_neg at hu
      obtain ⟨hux, huy, hut⟩ := hu
      rcases hw with rfl | rfl | rfl
      · exact AlmostDecisive.of_decisive
          (decisive_snd_of_almostDecisive hF hU hI (Ne.symm hxy) huy hux
            (key y w (Or.inr (Or.inl rfl)) (Or.inl rfl) (Ne.symm hxy)))
      · exact AlmostDecisive.of_decisive
          (decisive_snd_of_almostDecisive hF hU hI hxy hux huy
            (key x w (Or.inl rfl) (Or.inr (Or.inl rfl)) hxy))
      · exact AlmostDecisive.of_decisive
          (decisive_snd_of_almostDecisive hF hU hI (Ne.symm htx) hux hut
            (key x w (Or.inl rfl) (Or.inr (Or.inr rfl)) (Ne.symm htx)))
  exact decisive_fst_of_almostDecisive hF hU hI (Ne.symm hwu) (Ne.symm huv) (Ne.symm hwv) huw

end FieldExpansion

/-! ## Group contraction -/

/-- Comparing two rankings that agree on the ordered pair `(x, y)`. -/
theorem iff_pair {p q : A → A → Prop} (hp : IsRanking p) (hq : IsRanking q) {x y : A}
    (h1 : p x y) (h2 : q x y) : (p x y ↔ q x y) ∧ (p y x ↔ q y x) :=
  ⟨iff_of_true h1 h2, iff_of_false (hp.asymm h1) (hq.asymm h2)⟩

/-- Comparing two rankings that agree on the ordered pair `(y, x)`. -/
theorem iff_pair_swap {p q : A → A → Prop} (hp : IsRanking p) (hq : IsRanking q) {x y : A}
    (h1 : p y x) (h2 : q y x) : (p x y ↔ q x y) ∧ (p y x ↔ q y x) :=
  ⟨iff_of_false (hp.asymm h1) (hq.asymm h2), iff_of_true h1 h2⟩

section GroupContraction

variable {F : (V → A → A → Prop) → (A → A → Prop)} [DecidableEq V]

/-- **Group contraction**: if a coalition `S` is decisive and `i ∈ S`, then either `{i}`
or `S \ {i}` is almost decisive for some ordered pair. -/
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
theorem exists_singleton_decisive (hF : IsSWF F) (hU : Unanimity F) (hI : IIA F)
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (n : ℕ) (S : Finset V), S.card ≤ n → S.Nonempty →
      (∀ u v : A, u ≠ v → Decisive F S u v) →
      ∃ i : V, ∀ u v : A, u ≠ v → Decisive F ({i} : Finset V) u v := by
  intro n
  induction n with
  | zero =>
    intro S hcard hne _
    have := Finset.card_pos.mpr hne
    omega
  | succ n ih =>
    intro S hcard hne hdec
    by_cases h2 : 2 ≤ S.card
    · obtain ⟨i, hi⟩ := hne
      have hcard' : (S.erase i).card = S.card - 1 := Finset.card_erase_of_mem hi
      have hne' : (S.erase i).Nonempty := by
        rw [← Finset.card_pos, hcard']; omega
      rcases almostDecisive_split hF hI hab hac hbc hi hdec with hL | hR
      · exact ⟨i, decisive_all_of_almostDecisive hF hU hI hab hac hbc hac hL⟩
      · refine ih (S.erase i) (by omega) hne'
          (decisive_all_of_almostDecisive hF hU hI hab hac hbc (Ne.symm hbc) hR)
    · obtain ⟨i, rfl⟩ : ∃ i : V, S = {i} := by
        refine Finset.card_eq_one.mp ?_
        have := Finset.card_pos.mpr hne
        omega
      exact ⟨i, hdec⟩

end GroupContraction

/-! ## Arrow's theorem -/

section Main

variable {F : (V → A → A → Prop) → (A → A → Prop)}

/-- **Arrow's theorem** (positive form): with finitely many voters, at least one voter, and
at least three alternatives, every social welfare function satisfying unanimity and
independence of irrelevant alternatives has a dictator. -/
theorem exists_dictator [Fintype V] [Nonempty V] (hF : IsSWF F) (hU : Unanimity F) (hI : IIA F)
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ i : V, IsDictator F i := by
  classical
  have huniv : ∀ u v : A, u ≠ v → Decisive F (Finset.univ : Finset V) u v :=
    fun u v _ p hp hall => hU p hp u v (fun j => hall j (Finset.mem_univ j))
  obtain ⟨i, hi⟩ := exists_singleton_decisive hF hU hI hab hac hbc
    (Finset.univ : Finset V).card Finset.univ le_rfl Finset.univ_nonempty huniv
  refine ⟨i, fun p hp x y hxy => ?_⟩
  have hne : x ≠ y := by rintro rfl; exact (hp i).irrefl x hxy
  exact hi x y hne p hp (fun j hj => by
    rw [Finset.mem_singleton] at hj; subst hj; exact hxy)

/-- **Arrow's impossibility theorem**: for at least three alternatives and a finite,
nonempty electorate, no social welfare function satisfies unanimity, independence of
irrelevant alternatives and non-dictatorship simultaneously. -/
theorem arrow_impossibility [Fintype V] [Nonempty V]
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (F : (V → A → A → Prop) → (A → A → Prop)) (hF : IsSWF F) :
    ¬ (Unanimity F ∧ IIA F ∧ ∀ i : V, ¬ IsDictator F i) := by
  rintro ⟨hU, hI, hnd⟩
  obtain ⟨i, hi⟩ := exists_dictator hF hU hI hab hac hbc
  exact hnd i hi

/-- The hypotheses of Arrow's theorem are not vacuous: the rule that simply copies voter
`i`'s ranking is a social welfare function satisfying unanimity and IIA — and `i` is then
a dictator. -/
theorem dictatorial_isSWF_unanimity_iia (i : V) :
    IsSWF (fun p : V → A → A → Prop => p i) ∧ Unanimity (fun p : V → A → A → Prop => p i) ∧
      IIA (fun p : V → A → A → Prop => p i) ∧ IsDictator (fun p : V → A → A → Prop => p i) i :=
  ⟨fun _ hp => hp i, fun _ _ _ _ h => h i, fun _ _ _ _ _ _ h => (h i).1, fun _ _ _ _ h => h⟩

end Main

end Frontier

