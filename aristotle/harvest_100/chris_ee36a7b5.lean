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

open scoped Classical

/-- A strict preference relation on the set of alternatives `A`: a strict linear order,
given by a transitive, trichotomous, irreflexive relation. -/
structure StrictPref (A : Type*) where
  lt : A → A → Prop
  trans' : ∀ {x y z : A}, lt x y → lt y z → lt x z
  trichotomous' : ∀ x y : A, lt x y ∨ x = y ∨ lt y x
  irrefl' : ∀ x : A, ¬ lt x x

namespace StrictPref

variable {A : Type*}

theorem asymm (R : StrictPref A) {x y : A} (h : R.lt x y) : ¬ R.lt y x :=
  fun h' => R.irrefl' x (R.trans' h h')

end StrictPref

variable {ι A : Type*}

/-- A social welfare function is unanimous (Pareto) if it ranks `x` above `y` whenever
every voter does. -/
def Unanimity (f : (ι → StrictPref A) → StrictPref A) : Prop :=
  ∀ (P : ι → StrictPref A) (x y : A), (∀ i, (P i).lt x y) → (f P).lt x y

/-- Independence of irrelevant alternatives: the social ranking of the pair `x, y` depends
only on the voters' rankings of the pair `x, y`. -/
def IIA (f : (ι → StrictPref A) → StrictPref A) : Prop :=
  ∀ (P Q : ι → StrictPref A) (x y : A), (∀ i, ((P i).lt x y ↔ (Q i).lt x y)) →
    ((f P).lt x y ↔ (f Q).lt x y)

/-- Voter `i` is a dictator: society always follows `i`'s strict preferences. -/
def Dictator (f : (ι → StrictPref A) → StrictPref A) (i : ι) : Prop :=
  ∀ (P : ι → StrictPref A) (x y : A), (P i).lt x y → (f P).lt x y

/-! ## Building preferences -/

/-- The strict linear order obtained by ranking alternatives by a natural-number "tier",
breaking ties by a fixed well-ordering of `A`. -/
noncomputable def tierPref (t : A → ℕ) : StrictPref A where
  lt x y := t x < t y ∨ (t x = t y ∧ WellOrderingRel x y)
  trans' := by
    rintro x y z (h | ⟨h1, h2⟩) (h' | ⟨h1', h2'⟩)
    · exact Or.inl (lt_trans h h')
    · exact Or.inl (h1' ▸ h)
    · exact Or.inl (h1 ▸ h')
    · exact Or.inr ⟨h1.trans h1', Trans.trans h2 h2'⟩
  trichotomous' := by
    intro x y
    rcases lt_trichotomy (t x) (t y) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases trichotomous_of (WellOrderingRel (α := A)) x y with h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
    · exact Or.inr (Or.inr (Or.inl h))
  irrefl' := by
    rintro x (h | ⟨-, h⟩)
    · exact lt_irrefl _ h
    · exact irrefl_of _ _ h

/-- The preference which ranks `x` first, `y` second, `z` third, and all other
alternatives below. -/
noncomputable def pref3 (x y z : A) : StrictPref A :=
  tierPref (fun w => if w = x then 0 else if w = y then 1 else if w = z then 2 else 3)

theorem pref3_lt {x y z : A} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    (pref3 x y z).lt x y ∧ (pref3 x y z).lt y z ∧ (pref3 x y z).lt x z := by
  refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_⟩ <;>
    simp [hxy.symm, hyz.symm, hxz.symm]

/-! ## Decisive coalitions -/

variable (f : (ι → StrictPref A) → StrictPref A)

/-- The coalition `S` is decisive for the ordered pair `(x, y)`: whenever all members of `S`
prefer `x` to `y`, so does society (regardless of the other voters). -/
def Dec (S : Finset ι) (x y : A) : Prop :=
  ∀ P : ι → StrictPref A, (∀ i ∈ S, (P i).lt x y) → (f P).lt x y

/-- The coalition `S` is semi-decisive for the ordered pair `(x, y)`: whenever all members
of `S` prefer `x` to `y` and all non-members prefer `y` to `x`, society prefers `x` to `y`. -/
def SemiDec (S : Finset ι) (x y : A) : Prop :=
  ∀ P : ι → StrictPref A, (∀ i ∈ S, (P i).lt x y) → (∀ i, i ∉ S → (P i).lt y x) →
    (f P).lt x y

/-- `S` is decisive for every ordered pair of distinct alternatives. -/
def AllDec (S : Finset ι) : Prop := ∀ x y : A, x ≠ y → Dec f S x y

theorem semiDec_of_dec {S : Finset ι} {x y : A} (h : Dec f S x y) : SemiDec f S x y :=
  fun P hP _ => h P hP

/-- Field expansion, first form: semi-decisiveness over `(x,y)` spreads to full
decisiveness over `(x,z)`. -/
theorem dec_of_semiDec_right (hU : Unanimity f) (hIIA : IIA f) {S : Finset ι} {x y z : A}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (h : SemiDec f S x y) : Dec f S x z := by
  intro Q hQ
  obtain ⟨P, hP⟩ : ∃ P : ι → StrictPref A, ∀ i,
      P i = if i ∈ S then pref3 x y z else if (Q i).lt x z then pref3 y x z else pref3 y z x :=
    ⟨_, fun _ => rfl⟩
  have e0 : ∀ i, i ∈ S → P i = pref3 x y z := by
    intro i hi; rw [hP i, if_pos hi]
  have e1 : ∀ i, i ∉ S → (Q i).lt x z → P i = pref3 y x z := by
    intro i hi hc; rw [hP i, if_neg hi, if_pos hc]
  have e2 : ∀ i, i ∉ S → ¬ (Q i).lt x z → P i = pref3 y z x := by
    intro i hi hc; rw [hP i, if_neg hi, if_neg hc]
  have hs := pref3_lt hxy hyz hxz
  have ha := pref3_lt hxy.symm hxz hyz
  have hb := pref3_lt hyz hxz.symm hxy.symm
  have h1 : (f P).lt y z := by
    refine hU P y z (fun i => ?_)
    by_cases hi : i ∈ S
    · rw [e0 i hi]; exact hs.2.1
    · by_cases hc : (Q i).lt x z
      · rw [e1 i hi hc]; exact ha.2.2
      · rw [e2 i hi hc]; exact hb.1
  have h2 : (f P).lt x y := by
    refine h P (fun i hi => ?_) (fun i hi => ?_)
    · rw [e0 i hi]; exact hs.1
    · by_cases hc : (Q i).lt x z
      · rw [e1 i hi hc]; exact ha.1
      · rw [e2 i hi hc]; exact hb.2.2
  refine (hIIA P Q x z (fun i => ?_)).1 ((f P).trans' h2 h1)
  by_cases hi : i ∈ S
  · rw [e0 i hi]; exact iff_of_true hs.2.2 (hQ i hi)
  · by_cases hc : (Q i).lt x z
    · rw [e1 i hi hc]; exact iff_of_true ha.2.1 hc
    · rw [e2 i hi hc]; exact iff_of_false ((pref3 y z x).asymm hb.2.1) hc

/-- Field expansion, second form: semi-decisiveness over `(x,y)` spreads to full
decisiveness over `(z,y)`. -/
theorem dec_of_semiDec_left (hU : Unanimity f) (hIIA : IIA f) {S : Finset ι} {x y z : A}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (h : SemiDec f S x y) : Dec f S z y := by
  intro Q hQ
  obtain ⟨P, hP⟩ : ∃ P : ι → StrictPref A, ∀ i,
      P i = if i ∈ S then pref3 z x y else if (Q i).lt z y then pref3 z y x else pref3 y z x :=
    ⟨_, fun _ => rfl⟩
  have e0 : ∀ i, i ∈ S → P i = pref3 z x y := by
    intro i hi; rw [hP i, if_pos hi]
  have e1 : ∀ i, i ∉ S → (Q i).lt z y → P i = pref3 z y x := by
    intro i hi hc; rw [hP i, if_neg hi, if_pos hc]
  have e2 : ∀ i, i ∉ S → ¬ (Q i).lt z y → P i = pref3 y z x := by
    intro i hi hc; rw [hP i, if_neg hi, if_neg hc]
  have hs := pref3_lt hxz.symm hxy hyz.symm
  have ha := pref3_lt hyz.symm hxy.symm hxz.symm
  have hb := pref3_lt hyz hxz.symm hxy.symm
  have h1 : (f P).lt z x := by
    refine hU P z x (fun i => ?_)
    by_cases hi : i ∈ S
    · rw [e0 i hi]; exact hs.1
    · by_cases hc : (Q i).lt z y
      · rw [e1 i hi hc]; exact ha.2.2
      · rw [e2 i hi hc]; exact hb.2.1
  have h2 : (f P).lt x y := by
    refine h P (fun i hi => ?_) (fun i hi => ?_)
    · rw [e0 i hi]; exact hs.2.1
    · by_cases hc : (Q i).lt z y
      · rw [e1 i hi hc]; exact ha.2.1
      · rw [e2 i hi hc]; exact hb.2.2
  refine (hIIA P Q z y (fun i => ?_)).1 ((f P).trans' h1 h2)
  by_cases hi : i ∈ S
  · rw [e0 i hi]; exact iff_of_true hs.2.2 (hQ i hi)
  · by_cases hc : (Q i).lt z y
    · rw [e1 i hi hc]; exact iff_of_true ha.1 hc
    · rw [e2 i hi hc]; exact iff_of_false ((pref3 y z x).asymm hb.1) hc

/-- From semi-decisiveness over one pair of a triple, `S` is decisive over all six ordered
pairs of that triple. -/
theorem dec_triple (hU : Unanimity f) (hIIA : IIA f) {S : Finset ι} {x y z : A}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (h : SemiDec f S x y) :
    Dec f S x y ∧ Dec f S y x ∧ Dec f S x z ∧ Dec f S z x ∧ Dec f S y z ∧ Dec f S z y := by
  have dxz : Dec f S x z := dec_of_semiDec_right f hU hIIA hxy hyz hxz h
  have dyz : Dec f S y z :=
    dec_of_semiDec_left f hU hIIA hxz hyz.symm hxy (semiDec_of_dec f dxz)
  have dyx : Dec f S y x :=
    dec_of_semiDec_right f hU hIIA hyz hxz.symm hxy.symm (semiDec_of_dec f dyz)
  have dzx : Dec f S z x :=
    dec_of_semiDec_left f hU hIIA hxy.symm hxz hyz (semiDec_of_dec f dyx)
  have dzy : Dec f S z y :=
    dec_of_semiDec_right f hU hIIA hxz.symm hxy hyz.symm (semiDec_of_dec f dzx)
  have dxy : Dec f S x y :=
    dec_of_semiDec_left f hU hIIA hyz.symm hxy.symm hxz.symm (semiDec_of_dec f dzy)
  exact ⟨dxy, dyx, dxz, dzx, dyz, dzy⟩

theorem exists_third {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (p q : A) :
    ∃ r : A, r ≠ p ∧ r ≠ q := by
  by_cases h1 : a ≠ p ∧ a ≠ q
  · exact ⟨a, h1⟩
  by_cases h2 : b ≠ p ∧ b ≠ q
  · exact ⟨b, h2⟩
  rw [not_and_or, not_not, not_not] at h1 h2
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    rcases h1 with rfl | rfl
    · exact hac rfl
    · rcases h2 with rfl | rfl
      · exact hbc rfl
      · exact hab rfl
  · rintro rfl
    rcases h1 with rfl | rfl
    · rcases h2 with rfl | rfl
      · exact hab rfl
      · exact hbc rfl
    · exact hac rfl

/-- From semi-decisiveness over one pair, `S` is decisive over all pairs. -/
theorem allDec_of_semiDec (hU : Unanimity f) (hIIA : IIA f) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {S : Finset ι} {u v : A} (huv : u ≠ v)
    (h : SemiDec f S u v) : AllDec f S := by
  have six : ∀ z : A, z ≠ u → z ≠ v →
      Dec f S u v ∧ Dec f S v u ∧ Dec f S u z ∧ Dec f S z u ∧ Dec f S v z ∧ Dec f S z v :=
    fun z hzu hzv => dec_triple f hU hIIA huv (Ne.symm hzv) (Ne.symm hzu) h
  obtain ⟨r, hru, hrv⟩ := exists_third hab hac hbc u v
  intro p q hpq
  by_cases hpu : p = u
  · subst hpu
    by_cases hqv : q = v
    · subst hqv; exact (six r hru hrv).1
    · exact (six q (Ne.symm hpq) hqv).2.2.1
  · by_cases hpv : p = v
    · subst hpv
      by_cases hqu : q = u
      · subst hqu; exact (six r hru hrv).2.1
      · exact (six q hqu (Ne.symm hpq)).2.2.2.2.1
    · by_cases hqu : q = u
      · subst hqu; exact (six p hpu hpv).2.2.2.1
      · by_cases hqv : q = v
        · subst hqv; exact (six p hpu hpv).2.2.2.2.2
        · exact dec_of_semiDec_right f hU hIIA hpu (Ne.symm hqu) hpq
            (semiDec_of_dec f (six p hpu hpv).2.2.2.1)

/-- Group contraction: a decisive coalition split in two has a decisive half. -/
theorem allDec_split (hU : Unanimity f) (hIIA : IIA f) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {S S₁ S₂ : Finset ι}
    (hdisj : ∀ i, i ∈ S₁ → i ∉ S₂) (hunion : ∀ i, i ∈ S ↔ i ∈ S₁ ∨ i ∈ S₂)
    (hS : AllDec f S) : AllDec f S₁ ∨ AllDec f S₂ := by
  obtain ⟨P, hP⟩ : ∃ P : ι → StrictPref A, ∀ i,
      P i = if i ∈ S₁ then pref3 a b c else if i ∈ S₂ then pref3 c a b else pref3 b c a :=
    ⟨_, fun _ => rfl⟩
  have e0 : ∀ i, i ∈ S₁ → P i = pref3 a b c := by
    intro i hi; rw [hP i, if_pos hi]
  have e1 : ∀ i, i ∉ S₁ → i ∈ S₂ → P i = pref3 c a b := by
    intro i hi hj; rw [hP i, if_neg hi, if_pos hj]
  have e2 : ∀ i, i ∉ S₁ → i ∉ S₂ → P i = pref3 b c a := by
    intro i hi hj; rw [hP i, if_neg hi, if_neg hj]
  have h1 := pref3_lt hab hbc hac
  have h2 := pref3_lt (Ne.symm hac) hab (Ne.symm hbc)
  have h3 := pref3_lt hbc (Ne.symm hac) (Ne.symm hab)
  have hsoc : (f P).lt a b := by
    refine hS a b hab P (fun i hi => ?_)
    by_cases hi1 : i ∈ S₁
    · rw [e0 i hi1]; exact h1.1
    · rcases (hunion i).1 hi with hi' | hi2
      · exact absurd hi' hi1
      · rw [e1 i hi1 hi2]; exact h2.2.1
  rcases (f P).trichotomous' a c with hlt | heq | hgt
  · left
    refine allDec_of_semiDec f hU hIIA hab hac hbc hac ?_
    intro R hR1 hR2
    refine (hIIA P R a c (fun i => ?_)).1 hlt
    by_cases hi1 : i ∈ S₁
    · rw [e0 i hi1]; exact iff_of_true h1.2.2 (hR1 i hi1)
    · have hRi : ¬ (R i).lt a c := (R i).asymm (hR2 i hi1)
      by_cases hi2 : i ∈ S₂
      · rw [e1 i hi1 hi2]; exact iff_of_false ((pref3 c a b).asymm h2.1) hRi
      · rw [e2 i hi1 hi2]; exact iff_of_false ((pref3 b c a).asymm h3.2.1) hRi
  · exact absurd heq hac
  · right
    have hcb : (f P).lt c b := (f P).trans' hgt hsoc
    refine allDec_of_semiDec f hU hIIA hab hac hbc (Ne.symm hbc) ?_
    intro R hR1 hR2
    refine (hIIA P R c b (fun i => ?_)).1 hcb
    by_cases hi2 : i ∈ S₂
    · have hi1 : i ∉ S₁ := fun hx => hdisj i hx hi2
      rw [e1 i hi1 hi2]; exact iff_of_true h2.2.2 (hR1 i hi2)
    · have hRi : ¬ (R i).lt c b := (R i).asymm (hR2 i hi2)
      by_cases hi1 : i ∈ S₁
      · rw [e0 i hi1]; exact iff_of_false ((pref3 a b c).asymm h1.2.1) hRi
      · rw [e2 i hi1 hi2]; exact iff_of_false ((pref3 b c a).asymm h3.1) hRi

theorem exists_singleton_allDec (hU : Unanimity f) (hIIA : IIA f) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (n : ℕ) (S : Finset ι), S.card = n → S.Nonempty → AllDec f S →
      ∃ i : ι, AllDec f ({i} : Finset ι) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hcard hne hdec
    rcases eq_or_lt_of_le (Finset.one_le_card.2 hne) with hone | htwo
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hone.symm
      exact ⟨i, hi ▸ hdec⟩
    · obtain ⟨i, hiS⟩ := hne
      have hdisj : ∀ j, j ∈ ({i} : Finset ι) → j ∉ S.erase i := by
        intro j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        simp
      have hunion : ∀ j, j ∈ S ↔ j ∈ ({i} : Finset ι) ∨ j ∈ S.erase i := by
        intro j
        simp only [Finset.mem_singleton, Finset.mem_erase]
        by_cases hji : j = i
        · subst hji; simp [hiS]
        · simp [hji]
      rcases allDec_split f hU hIIA hab hac hbc hdisj hunion hdec with hL | hR
      · exact ⟨i, hL⟩
      · refine ih (S.erase i).card ?_ (S.erase i) rfl ?_ hR
        · rw [← hcard]; exact Finset.card_erase_lt_of_mem hiS
        · refine Finset.card_pos.1 ?_
          rw [Finset.card_erase_of_mem hiS]
          omega

theorem dictator_of_allDec_singleton {i : ι} (h : AllDec f ({i} : Finset ι)) : Dictator f i := by
  intro P x y hxy
  by_cases hne : x = y
  · subst hne; exact absurd hxy ((P i).irrefl' x)
  · refine h x y hne P (fun j hj => ?_)
    rw [Finset.mem_singleton] at hj
    subst hj
    exact hxy

theorem not_allDec_empty {a b : A} (hab : a ≠ b)
    (h : AllDec f (∅ : Finset ι)) : False := by
  have P : ι → StrictPref A := fun _ => tierPref (fun _ => 0)
  have h1 := h a b hab P (by simp)
  have h2 := h b a (Ne.symm hab) P (by simp)
  exact (f P).asymm h1 h2

/-! ## Arrow's impossibility theorem -/

/-- **Arrow's impossibility theorem.** With finitely many voters and at least three
alternatives, no social welfare function satisfies unanimity, independence of irrelevant
alternatives, and non-dictatorship. -/
theorem arrow_impossibility [Fintype ι] (hA : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (f : (ι → StrictPref A) → StrictPref A) :
    ¬ (Unanimity f ∧ IIA f ∧ ¬ ∃ i : ι, Dictator f i) := by
  rintro ⟨hU, hIIA, hnd⟩
  obtain ⟨a, b, c, hab, hac, hbc⟩ := hA
  have huniv : AllDec f (Finset.univ : Finset ι) :=
    fun x y _ P hP => hU P x y (fun i => hP i (Finset.mem_univ i))
  by_cases hne : (Finset.univ : Finset ι).Nonempty
  · obtain ⟨i, hi⟩ :=
      exists_singleton_allDec f hU hIIA hab hac hbc _ _ rfl hne huniv
    exact hnd ⟨i, dictator_of_allDec_singleton f hi⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact not_allDec_empty f hab (hne ▸ huniv)

/-- Sanity check (the hypotheses of Arrow's theorem are not vacuous): the dictatorial rule
"always copy voter `i₀`'s ranking" is unanimous and satisfies IIA. -/
theorem projection_unanimity_iia (i₀ : ι) :
    Unanimity (fun P : ι → StrictPref A => P i₀) ∧ IIA (fun P : ι → StrictPref A => P i₀) ∧
      Dictator (fun P : ι → StrictPref A => P i₀) i₀ :=
  ⟨fun _ _ _ h => h i₀, fun _ _ _ _ h => h i₀, fun _ _ _ h => h⟩

/-- Equivalent positive form: a unanimous social welfare function satisfying IIA over at
least three alternatives has a dictator. -/
theorem arrow_dictator [Fintype ι] (hA : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (f : (ι → StrictPref A) → StrictPref A) (hU : Unanimity f) (hIIA : IIA f) :
    ∃ i : ι, Dictator f i := by
  by_contra hcon
  exact arrow_impossibility hA f ⟨hU, hIIA, hcon⟩

end Frontier

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

