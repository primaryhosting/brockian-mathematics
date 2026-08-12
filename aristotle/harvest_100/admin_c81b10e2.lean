import Mathlib

/-!
# Preference relations for Arrow's impossibility theorem

`Pref A` is a weak preference relation on the set of alternatives `A`: a total preorder,
where `r.le a b` means "`b` is at least as good as `a`" (higher is better).

`LinPref A` is a *ranking*: a weak preference with no ties (an antisymmetric total preorder,
i.e. a linear order).

This file develops the basic API together with the constructions of rankings that are used
in the proof of Arrow's theorem.
-/

open scoped Classical

namespace Frontier

/-- A weak preference relation on `A`: a total preorder.
`r.le a b` means "`b` is at least as good as `a`". -/
structure Pref (A : Type*) where
  /-- `le a b` means "`b` is at least as good as `a`". -/
  le : A → A → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c : A}, le a b → le b c → le a c
  le_total : ∀ a b, le a b ∨ le b a

/-- A ranking of the alternatives: a weak preference with no ties. -/
structure LinPref (A : Type*) extends Pref A where
  le_antisymm : ∀ {a b : A}, le a b → le b a → a = b

namespace Pref

variable {A : Type*} (r : Pref A)

/-- Strict preference: `r.lt a b` means "`b` is strictly better than `a`". -/
def lt (a b : A) : Prop := ¬ r.le b a

variable {r}

theorem not_lt_iff {a b : A} : ¬ r.lt a b ↔ r.le b a := not_not

theorem lt_irrefl (a : A) : ¬ r.lt a a := fun h => h (r.le_refl a)

theorem le_of_lt {a b : A} (h : r.lt a b) : r.le a b :=
  (r.le_total a b).resolve_right h

theorem ne_of_lt {a b : A} (h : r.lt a b) : a ≠ b := by
  rintro rfl; exact lt_irrefl a h

theorem lt_of_lt_of_le {a b c : A} (h₁ : r.lt a b) (h₂ : r.le b c) : r.lt a c :=
  fun h => h₁ (r.le_trans h₂ h)

theorem lt_of_le_of_lt {a b c : A} (h₁ : r.le a b) (h₂ : r.lt b c) : r.lt a c :=
  fun h => h₂ (r.le_trans h h₁)

theorem lt_trans {a b c : A} (h₁ : r.lt a b) (h₂ : r.lt b c) : r.lt a c :=
  lt_of_le_of_lt (le_of_lt h₁) h₂

theorem lt_asymm {a b : A} (h : r.lt a b) : ¬ r.lt b a := fun h' => h' (le_of_lt h)

/-- `b` is the strictly best alternative. -/
def IsTop (b : A) : Prop := ∀ x, x ≠ b → r.lt x b

/-- `b` is the strictly worst alternative. -/
def IsBot (b : A) : Prop := ∀ x, x ≠ b → r.lt b x

theorem IsTop.le {b : A} (h : r.IsTop b) (x : A) : r.le x b := by
  rcases eq_or_ne x b with rfl | hx
  · exact r.le_refl x
  · exact le_of_lt (h x hx)

theorem IsBot.le {b : A} (h : r.IsBot b) (x : A) : r.le b x := by
  rcases eq_or_ne x b with rfl | hx
  · exact r.le_refl x
  · exact le_of_lt (h x hx)

theorem IsTop.not_le {b : A} (h : r.IsTop b) {x : A} (hx : x ≠ b) : ¬ r.le b x := h x hx

theorem IsBot.not_le {b : A} (h : r.IsBot b) {x : A} (hx : x ≠ b) : ¬ r.le x b := h x hx

theorem IsTop.not_isBot {b x : A} (hx : x ≠ b) (h : r.IsTop b) : ¬ r.IsBot b := by
  intro h'
  exact (h x hx) (le_of_lt (h' x hx))

end Pref

namespace LinPref

variable {A : Type*} (r : LinPref A)

theorem lt_or_lt {a b : A} (h : a ≠ b) : r.lt a b ∨ r.lt b a := by
  rcases r.le_total a b with hab | hba
  · left
    intro hba
    exact h (r.le_antisymm hab hba)
  · right
    intro hab
    exact h (r.le_antisymm hab hba)

theorem lt_of_le_of_ne {a b : A} (h : r.le a b) (hne : a ≠ b) : r.lt a b := by
  intro hba
  exact hne (r.le_antisymm h hba)

theorem le_iff_lt_or_eq {a b : A} : r.le a b ↔ r.lt a b ∨ a = b := by
  constructor
  · intro h
    rcases eq_or_ne a b with rfl | hne
    · exact Or.inr rfl
    · exact Or.inl (r.lt_of_le_of_ne h hne)
  · rintro (h | rfl)
    · exact Pref.le_of_lt h
    · exact r.le_refl a

theorem IsTop.eq_of_le {b : A} (h : r.toPref.IsTop b) {x : A} (hbx : r.le b x) : x = b := by
  by_contra hx
  exact (h x hx) hbx

/-- Lexicographic refinement: rank first by the score `f` (higher is better), breaking ties
using `r`. -/
def lex (r : LinPref A) (f : A → ℕ) : LinPref A where
  le a b := f a < f b ∨ (f a = f b ∧ r.le a b)
  le_refl a := Or.inr ⟨rfl, r.le_refl a⟩
  le_trans := by
    rintro a b c (h₁ | ⟨h₁, h₁'⟩) (h₂ | ⟨h₂, h₂'⟩)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, r.le_trans h₁' h₂'⟩
  le_total a b := by
    rcases lt_trichotomy (f a) (f b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases r.le_total a b with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inr (Or.inl h)
  le_antisymm := by
    rintro a b (h₁ | ⟨h₁, h₁'⟩) (h₂ | ⟨h₂, h₂'⟩)
    · omega
    · omega
    · omega
    · exact r.le_antisymm h₁' h₂'

@[simp] theorem lex_le {r : LinPref A} {f : A → ℕ} {a b : A} :
    (r.lex f).le a b ↔ (f a < f b ∨ (f a = f b ∧ r.le a b)) := Iff.rfl

theorem lex_lt {r : LinPref A} {f : A → ℕ} {a b : A} :
    (r.lex f).lt a b ↔ (f a < f b ∨ (f a = f b ∧ r.lt a b)) := by
  simp only [Pref.lt, lex_le, not_or, not_and]
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases lt_trichotomy (f a) (f b) with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', h₂ h'.symm⟩
    · exact absurd h' (by omega)
  · rintro (h | ⟨h, h'⟩)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, fun _ => h'⟩

/-- Precomposition of a ranking with a permutation of the alternatives. -/
def comp (r : LinPref A) (e : Equiv.Perm A) : LinPref A where
  le a b := r.le (e a) (e b)
  le_refl _ := r.le_refl _
  le_trans h₁ h₂ := r.le_trans h₁ h₂
  le_total _ _ := r.le_total _ _
  le_antisymm h₁ h₂ := e.injective (r.le_antisymm h₁ h₂)

@[simp] theorem comp_le {r : LinPref A} {e : Equiv.Perm A} {a b : A} :
    (r.comp e).le a b ↔ r.le (e a) (e b) := Iff.rfl

/-- The ranking `r` modified by moving `b` to the top. -/
noncomputable def topPref (r : LinPref A) (b : A) : LinPref A :=
  r.lex (fun x => if x = b then 1 else 0)

/-- The ranking `r` modified by moving `b` to the bottom. -/
noncomputable def botPref (r : LinPref A) (b : A) : LinPref A :=
  r.lex (fun x => if x = b then 0 else 1)

/-- The ranking `r` modified by moving `b` to the position just below `a`. -/
noncomputable def midPref (r : LinPref A) (b a : A) : LinPref A :=
  r.lex (fun x => if x = b then 1 else if r.le a x then 2 else 0)

theorem topPref_isTop (r : LinPref A) (b : A) : (r.topPref b).toPref.IsTop b := by
  intro x hx
  refine lex_lt.mpr (Or.inl ?_)
  simp [hx]

theorem botPref_isBot (r : LinPref A) (b : A) : (r.botPref b).toPref.IsBot b := by
  intro x hx
  refine lex_lt.mpr (Or.inl ?_)
  simp [hx]

theorem topPref_le_of_ne (r : LinPref A) {b x y : A} (hx : x ≠ b) (hy : y ≠ b) :
    (r.topPref b).le x y ↔ r.le x y := by
  simp [topPref, hx, hy]

theorem botPref_le_of_ne (r : LinPref A) {b x y : A} (hx : x ≠ b) (hy : y ≠ b) :
    (r.botPref b).le x y ↔ r.le x y := by
  simp [botPref, hx, hy]

theorem midPref_le_of_ne (r : LinPref A) {b a x y : A} (hx : x ≠ b) (hy : y ≠ b) :
    (r.midPref b a).le x y ↔ r.le x y := by
  simp only [midPref, lex_le, if_neg hx, if_neg hy]
  by_cases hax : r.le a x <;> by_cases hay : r.le a y <;>
    simp only [hax, hay, if_true, if_false]
  · simp
  · exact iff_of_false (by simp) (fun h => hay (r.le_trans hax h))
  · exact iff_of_true (Or.inl (by omega)) (r.le_trans ((r.le_total a x).resolve_left hax) hay)
  · simp

/-- In `r.midPref b a`, the alternative `a` is strictly better than `b`. -/
theorem midPref_lt_top (r : LinPref A) {b a : A} (hab : a ≠ b) : (r.midPref b a).lt b a := by
  refine lex_lt.mpr (Or.inl ?_)
  simp [hab, r.le_refl a]

/-- In `r.midPref b a`, anything strictly below `a` in `r` is strictly below `b`. -/
theorem midPref_lt_bot (r : LinPref A) {b a c : A} (hcb : c ≠ b) (h : r.lt c a) :
    (r.midPref b a).lt c b := by
  have hac : ¬ r.le a c := h
  refine lex_lt.mpr (Or.inl ?_)
  simp [hcb, hac]

end LinPref

end Frontier

import Mathlib
import RequestProject.Basic
import RequestProject.Arrow

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

import RequestProject.Basic

/-!
# Arrow's impossibility theorem

A *social welfare function* `F : SWF V A` aggregates, for each profile of individual rankings
of the alternatives `A` (one ranking `P i : LinPref A` per voter `i : V`), a social weak
preference `F P : Pref A`.

We prove: if there are at least three alternatives and finitely many (at least one) voters, then
no social welfare function satisfies unanimity (Pareto), independence of irrelevant alternatives
and non-dictatorship.
-/

open scoped Classical

namespace Frontier

variable {V A : Type*}

/-- A social welfare function: it maps every profile of individual rankings (strict linear
preferences, i.e. the unrestricted domain) to a social weak preference. -/
def SWF (V A : Type*) : Type _ := (V → LinPref A) → Pref A

/-- Unanimity (the Pareto condition): if every voter strictly prefers `b` to `a`, then so
does society. -/
def Unanimity (F : SWF V A) : Prop :=
  ∀ (P : V → LinPref A) (a b : A), (∀ i, (P i).lt a b) → (F P).lt a b

/-- Independence of irrelevant alternatives: the social preference between `a` and `b` depends
only on the individual preferences between `a` and `b`. -/
def IIA (F : SWF V A) : Prop :=
  ∀ (P Q : V → LinPref A) (a b : A), (∀ i, ((P i).le a b ↔ (Q i).le a b)) →
    ((F P).le a b ↔ (F Q).le a b)

/-- Voter `i` is a dictator: society always strictly follows `i`'s strict preferences. -/
def IsDictator (F : SWF V A) (i : V) : Prop :=
  ∀ (P : V → LinPref A) (a b : A), (P i).lt a b → (F P).lt a b

/-- Voter `i` is decisive on all pairs of alternatives avoiding `b`. -/
def DecisiveOff (F : SWF V A) (i : V) (b : A) : Prop :=
  ∀ (P : V → LinPref A) (x y : A), x ≠ b → y ≠ b → (P i).lt x y → (F P).lt x y

/-- There are at least three alternatives. -/
def ThreeAlternatives (A : Type*) : Prop := ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z

/-! ### Auxiliary constructions -/

/-- The ranking associated with a linear order. -/
def LinPref.ofLinearOrder (A : Type*) [LinearOrder A] : LinPref A where
  le a b := a ≤ b
  le_refl a := _root_.le_refl a
  le_trans h₁ h₂ := _root_.le_trans h₁ h₂
  le_total a b := _root_.le_total a b
  le_antisymm h₁ h₂ := _root_.le_antisymm h₁ h₂

/-- Some fixed ranking of the alternatives, used as a background order. -/
noncomputable def baseLinPref (A : Type*) : LinPref A :=
  letI : LinearOrder A := IsWellOrder.linearOrder (WellOrderingRel (α := A))
  LinPref.ofLinearOrder A

theorem exists_ne_ne (h3 : ThreeAlternatives A) (p q : A) : ∃ d : A, d ≠ p ∧ d ≠ q := by
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := h3
  by_contra h
  push_neg at h
  have key : ∀ w : A, w = p ∨ w = q := by
    intro w
    rcases eq_or_ne w p with h' | h'
    · exact Or.inl h'
    · exact Or.inr (h w h')
  rcases key x with h1 | h1 <;> rcases key y with h2 | h2 <;> rcases key z with h3' | h3' <;>
    simp_all

/-- At least three alternatives, in terms of cardinality. -/
theorem threeAlternatives_of_three_le_card [Fintype A] (h : 3 ≤ Fintype.card A) :
    ThreeAlternatives A := by
  have h' : 3 ≤ (Finset.univ : Finset A).card := by simpa using h
  obtain ⟨s, -, hcard⟩ := Finset.exists_subset_card_eq h'
  obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := Finset.card_eq_three.mp hcard
  exact ⟨x, y, z, hxy, hxz, hyz⟩

/-! ### The extremal lemma -/

/-- **Extremal lemma**: if in every voter's ranking `b` is either the best or the worst
alternative, then `b` is either socially best or socially worst. -/
theorem extremal_lemma {F : SWF V A} (hU : Unanimity F) (hI : IIA F)
    (h3 : ThreeAlternatives A) (b : A) (P : V → LinPref A)
    (hext : ∀ i, (P i).toPref.IsTop b ∨ (P i).toPref.IsBot b) :
    (F P).IsTop b ∨ (F P).IsBot b := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnt, hnb⟩ := hcon
  obtain ⟨u, hub, hu⟩ : ∃ u, u ≠ b ∧ (F P).le b u := by
    by_contra h
    push_neg at h
    exact hnt fun x hx => h x hx
  obtain ⟨v, hvb, hv⟩ : ∃ v, v ≠ b ∧ (F P).le v b := by
    by_contra h
    push_neg at h
    exact hnb fun x hx => h x hx
  -- find two *distinct* alternatives `X ≠ Y`, both different from `b`, with `b ≤ X` and `Y ≤ b`
  obtain ⟨X, Y, hXb, hYb, hXY, hbX, hYble⟩ :
      ∃ X Y : A, X ≠ b ∧ Y ≠ b ∧ X ≠ Y ∧ (F P).le b X ∧ (F P).le Y b := by
    rcases eq_or_ne u v with rfl | huv
    · obtain ⟨d, hdu, hdb⟩ := exists_ne_ne h3 u b
      rcases (F P).le_total d b with hdb' | hbd
      · exact ⟨u, d, hub, hdb, fun h => hdu h.symm, hu, hdb'⟩
      · exact ⟨d, u, hdb, hub, hdu, hbd, hv⟩
    · exact ⟨u, v, hub, hvb, huv, hu, hv⟩
  -- move `Y` above `X` in every voter's ranking, without touching the comparisons with `b`
  set e : Equiv.Perm A := Equiv.swap X Y with he
  set P' : V → LinPref A := fun i => if (P i).lt X Y then P i else (P i).comp e with hP'
  have heX : e X = Y := Equiv.swap_apply_left X Y
  have heY : e Y = X := Equiv.swap_apply_right X Y
  have heb : e b = b := Equiv.swap_apply_of_ne_of_ne (fun h => hXb h.symm) (fun h => hYb h.symm)
  have hstrict : ∀ i, (P' i).lt X Y := by
    intro i
    by_cases h : (P i).lt X Y
    · simp [hP', h]
    · have hYX : (P i).le Y X := Pref.not_lt_iff.mp h
      have : ¬ (P i).le X Y := fun h' => hXY ((P i).le_antisymm h' hYX)
      have hPi : P' i = (P i).comp e := by simp only [hP', if_neg h]
      rw [hPi]
      show ¬ ((P i).comp e).le Y X
      rw [LinPref.comp_le, heY, heX]
      exact this
  have hpair1 : ∀ i, (P' i).le b X ↔ (P i).le b X := by
    intro i
    by_cases h : (P i).lt X Y
    · simp [hP', h]
    · have : (P' i).le b X ↔ (P i).le b Y := by simp [hP', h, LinPref.comp, heX, heb]
      rw [this]
      rcases hext i with htop | hbot
      · exact iff_of_false (htop.not_le (fun h' => hYb h')) (htop.not_le (fun h' => hXb h'))
      · exact iff_of_true (hbot.le Y) (hbot.le X)
  have hpair2 : ∀ i, (P' i).le Y b ↔ (P i).le Y b := by
    intro i
    by_cases h : (P i).lt X Y
    · simp [hP', h]
    · have : (P' i).le Y b ↔ (P i).le X b := by simp [hP', h, LinPref.comp, heY, heb]
      rw [this]
      rcases hext i with htop | hbot
      · exact iff_of_true (htop.le X) (htop.le Y)
      · exact iff_of_false (hbot.not_le (fun h' => hXb h')) (hbot.not_le (fun h' => hYb h'))
  have h1 : (F P').le b X := (hI P' P b X hpair1).mpr hbX
  have h2 : (F P').le Y b := (hI P' P Y b hpair2).mpr hYble
  exact hU P' X Y hstrict ((F P').le_trans h2 h1)

/-! ### The pivotal voter -/

/-- **Pivotal voter**: with finitely many voters (indexed by `Fin n`, `n > 0`), for each
alternative `b` there is a voter who is decisive on every pair of alternatives avoiding `b`. -/
theorem exists_decisiveOff {n : ℕ} (hn : 0 < n) (h3 : ThreeAlternatives A)
    {F : SWF (Fin n) A} (hU : Unanimity F) (hI : IIA F) (b : A) :
    ∃ i : Fin n, DecisiveOff F i b := by
  set r0 : LinPref A := baseLinPref A with hr0
  set Pk : ℕ → Fin n → LinPref A :=
    fun k i => if (i : ℕ) < k then r0.topPref b else r0.botPref b with hPk
  have hPkTop : ∀ (k : ℕ) (i : Fin n), (i : ℕ) < k → Pk k i = r0.topPref b := by
    intro k i h; simp [hPk, h]
  have hPkBot : ∀ (k : ℕ) (i : Fin n), ¬ (i : ℕ) < k → Pk k i = r0.botPref b := by
    intro k i h; simp [hPk, h]
  have hext : ∀ (k : ℕ) (i : Fin n), (Pk k i).toPref.IsTop b ∨ (Pk k i).toPref.IsBot b := by
    intro k i
    by_cases h : (i : ℕ) < k
    · exact Or.inl (by rw [hPkTop k i h]; exact r0.topPref_isTop b)
    · exact Or.inr (by rw [hPkBot k i h]; exact r0.botPref_isBot b)
  have hTopn : (F (Pk n)).IsTop b := by
    intro x hx
    refine hU (Pk n) x b (fun i => ?_)
    rw [hPkTop n i i.isLt]
    exact r0.topPref_isTop b x hx
  have hexists : ∃ k, (F (Pk k)).IsTop b := ⟨n, hTopn⟩
  set m : ℕ := Nat.find hexists with hmdef
  have hm : (F (Pk m)).IsTop b := Nat.find_spec hexists
  have hmn : m ≤ n := Nat.find_le hTopn
  have hBot0 : (F (Pk 0)).IsBot b := by
    intro x hx
    refine hU (Pk 0) b x (fun i => ?_)
    rw [hPkBot 0 i (by omega)]
    exact r0.botPref_isBot b x hx
  obtain ⟨d, hdb, -⟩ := exists_ne_ne h3 b b
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    exact (hm d hdb) (Pref.le_of_lt (hBot0 d hdb))
  have hprev : ¬ (F (Pk (m - 1))).IsTop b := Nat.find_min hexists (by omega)
  have hprevBot : (F (Pk (m - 1))).IsBot b :=
    (extremal_lemma hU hI h3 b (Pk (m - 1)) (hext (m - 1))).resolve_left hprev
  refine ⟨⟨m - 1, by omega⟩, ?_⟩
  set i0 : Fin n := ⟨m - 1, by omega⟩ with hi0
  have hi0val : (i0 : ℕ) = m - 1 := rfl
  intro Q x y hx hy hxy
  set Q' : Fin n → LinPref A := fun j =>
    if (j : ℕ) < m - 1 then (Q j).topPref b
    else if (j : ℕ) = m - 1 then (Q j).midPref b y
    else (Q j).botPref b with hQ'
  -- society ranks `y` strictly above `b`
  have step1 : ¬ (F Q').le y b := by
    have hagree : ∀ j, (Q' j).le y b ↔ (Pk (m - 1) j).le y b := by
      intro j
      rcases lt_trichotomy ((j : ℕ)) (m - 1) with h | h | h
      · rw [hPkTop (m - 1) j h]
        simp only [hQ', if_pos h]
        exact iff_of_true (((Q j).topPref_isTop b).le y) ((r0.topPref_isTop b).le y)
      · rw [hPkBot (m - 1) j (by omega)]
        simp only [hQ', if_neg (by omega : ¬ (j : ℕ) < m - 1), if_pos h]
        exact iff_of_false ((Q j).midPref_lt_top hy) (((r0.botPref_isBot b)).not_le hy)
      · rw [hPkBot (m - 1) j (by omega)]
        simp only [hQ', if_neg (by omega : ¬ (j : ℕ) < m - 1),
          if_neg (by omega : ¬ (j : ℕ) = m - 1)]
        exact iff_of_false (((Q j).botPref_isBot b).not_le hy)
          (((r0.botPref_isBot b)).not_le hy)
    rw [hI Q' (Pk (m - 1)) y b hagree]
    exact hprevBot.not_le hy
  -- society ranks `b` weakly above `x`
  have step2 : (F Q').le x b := by
    have hagree : ∀ j, (Q' j).le x b ↔ (Pk m j).le x b := by
      intro j
      rcases lt_trichotomy ((j : ℕ)) (m - 1) with h | h | h
      · rw [hPkTop m j (by omega)]
        simp only [hQ', if_pos h]
        exact iff_of_true (((Q j).topPref_isTop b).le x) ((r0.topPref_isTop b).le x)
      · rw [hPkTop m j (by omega)]
        simp only [hQ', if_neg (by omega : ¬ (j : ℕ) < m - 1), if_pos h]
        have hQj : Q j = Q i0 := by
          congr 1
          exact Fin.ext (by simp [hi0val, h])
        refine iff_of_true ?_ ((r0.topPref_isTop b).le x)
        rw [hQj]
        exact Pref.le_of_lt ((Q i0).midPref_lt_bot hx hxy)
      · rw [hPkBot m j (by omega)]
        simp only [hQ', if_neg (by omega : ¬ (j : ℕ) < m - 1),
          if_neg (by omega : ¬ (j : ℕ) = m - 1)]
        exact iff_of_false (((Q j).botPref_isBot b).not_le hx)
          (((r0.botPref_isBot b)).not_le hx)
    rw [hI Q' (Pk m) x b hagree]
    exact hm.le x
  have step3 : (F Q').lt x y := fun hyx => step1 ((F Q').le_trans hyx step2)
  -- `Q'` and `Q` agree on the pair `{x, y}`
  have hagree : ∀ j, (Q' j).le y x ↔ (Q j).le y x := by
    intro j
    rcases lt_trichotomy ((j : ℕ)) (m - 1) with h | h | h
    · simp only [hQ', if_pos h]
      exact (Q j).topPref_le_of_ne hy hx
    · simp only [hQ', if_neg (by omega : ¬ (j : ℕ) < m - 1), if_pos h]
      exact (Q j).midPref_le_of_ne hy hx
    · simp only [hQ', if_neg (by omega : ¬ (j : ℕ) < m - 1),
        if_neg (by omega : ¬ (j : ℕ) = m - 1)]
      exact (Q j).botPref_le_of_ne hy hx
  intro hyx
  exact step3 ((hI Q Q' y x (fun j => (hagree j).symm)).mp hyx)

/-! ### From local decisiveness to dictatorship -/

/-- Two voters that are decisive off two different alternatives must be the same voter. -/
theorem decisiveOff_unique {F : SWF V A} (hU : Unanimity F)
    (h3 : ThreeAlternatives A) {b c : A} (hbc : b ≠ c) {i j : V}
    (hi : DecisiveOff F i b) (hj : DecisiveOff F j c) : i = j := by
  by_contra hij
  obtain ⟨d, hdb, hdc⟩ := exists_ne_ne h3 b c
  set r0 : LinPref A := baseLinPref A with hr0
  set ri : LinPref A := r0.lex (fun t => if t = d then 3 else if t = c then 2 else
    if t = b then 1 else 0) with hri
  set ro : LinPref A := r0.lex (fun t => if t = c then 3 else if t = b then 2 else
    if t = d then 1 else 0) with hro
  set Q : V → LinPref A := fun k => if k = i then ri else ro with hQ
  have hcd : c ≠ d := fun h => hdc h.symm
  have hbd : b ≠ d := fun h => hdb h.symm
  have hcb : c ≠ b := Ne.symm hbc
  -- voter `i` strictly prefers `d` to `c`
  have h1 : (F Q).lt c d := by
    refine hi Q c d hcb hdb ?_
    simp only [hQ, if_pos rfl]
    refine LinPref.lex_lt.mpr (Or.inl ?_)
    simp [hcd]
  -- voter `j` strictly prefers `b` to `d`
  have h2 : (F Q).lt d b := by
    refine hj Q d b hdc hbc ?_
    simp only [hQ, if_neg (Ne.symm hij)]
    refine LinPref.lex_lt.mpr (Or.inl ?_)
    simp [hdc, hdb, hbc]
  -- but everybody strictly prefers `c` to `b`
  have h3' : (F Q).lt b c := by
    refine hU Q b c (fun k => ?_)
    by_cases hk : k = i
    · simp only [hQ, if_pos hk]
      refine LinPref.lex_lt.mpr (Or.inl ?_)
      simp [hbd, hbc, hcd]
    · simp only [hQ, if_neg hk]
      refine LinPref.lex_lt.mpr (Or.inl ?_)
      simp [hbc]
  exact (Pref.lt_asymm h3') (Pref.lt_trans h1 h2)

/-- A voter decisive off some alternative, in the presence of at least three alternatives,
is a dictator. -/
theorem isDictator_of_decisiveOff {F : SWF V A} (hU : Unanimity F)
    (h3 : ThreeAlternatives A) (hdec : ∀ b : A, ∃ i : V, DecisiveOff F i b)
    {b : A} {i : V} (hi : DecisiveOff F i b) : IsDictator F i := by
  intro P x y hxy
  by_cases hb : x ≠ b ∧ y ≠ b
  · exact hi P x y hb.1 hb.2 hxy
  · obtain ⟨c, hcx, hcy⟩ := exists_ne_ne h3 x y
    have hcb : c ≠ b := by
      rcases not_and_or.mp hb with h | h
      · rw [not_not] at h; rw [← h]; exact hcx
      · rw [not_not] at h; rw [← h]; exact hcy
    obtain ⟨j, hj⟩ := hdec c
    have hij : i = j := decisiveOff_unique hU h3 (Ne.symm hcb) hi hj
    subst hij
    exact hj P x y (Ne.symm hcx) (Ne.symm hcy) hxy

/-! ### Arrow's theorem -/

/-- Arrow's theorem for `n > 0` voters indexed by `Fin n`: unanimity and IIA force a dictator. -/
theorem exists_dictator_fin {n : ℕ} (hn : 0 < n) (h3 : ThreeAlternatives A)
    {F : SWF (Fin n) A} (hU : Unanimity F) (hI : IIA F) : ∃ i : Fin n, IsDictator F i := by
  obtain ⟨x, -, -, -, -, -⟩ := id h3
  have hdec : ∀ b : A, ∃ i : Fin n, DecisiveOff F i b := fun b =>
    exists_decisiveOff hn h3 hU hI b
  obtain ⟨i, hi⟩ := hdec x
  exact ⟨i, isDictator_of_decisiveOff hU h3 hdec hi⟩

/-- **Arrow's theorem**: for a finite nonempty set of voters and at least three alternatives,
every social welfare function satisfying unanimity and independence of irrelevant alternatives
has a dictator. -/
theorem exists_dictator [Fintype V] [Nonempty V] (h3 : ThreeAlternatives A)
    {F : SWF V A} (hU : Unanimity F) (hI : IIA F) : ∃ i : V, IsDictator F i := by
  classical
  set n : ℕ := Fintype.card V with hn'
  set e : V ≃ Fin n := Fintype.equivFin V with he
  have hn : 0 < n := Fintype.card_pos
  set G : SWF (Fin n) A := fun P => F (fun i => P (e i)) with hG
  have hUG : Unanimity G := fun P a b h => hU _ a b (fun i => h (e i))
  have hIG : IIA G := fun P Q a b h => hI _ _ a b (fun i => h (e i))
  obtain ⟨j, hj⟩ := exists_dictator_fin hn h3 hUG hIG
  refine ⟨e.symm j, fun P a b hab => ?_⟩
  have key := hj (fun k => P (e.symm k)) a b hab
  simp only [hG, Equiv.symm_apply_apply] at key
  exact key

/-- **Arrow's impossibility theorem**: with at least three alternatives and finitely many
(at least one) voters, no social welfare function satisfies unanimity, independence of
irrelevant alternatives and non-dictatorship. -/
theorem arrow_impossibility [Fintype V] [Nonempty V] (h3 : ThreeAlternatives A)
    (F : SWF V A) : ¬ (Unanimity F ∧ IIA F ∧ ∀ i : V, ¬ IsDictator F i) := by
  rintro ⟨hU, hI, hnd⟩
  obtain ⟨i, hi⟩ := exists_dictator h3 hU hI
  exact hnd i hi

/-- **Arrow's impossibility theorem**, stated for a finite set of at least three alternatives. -/
theorem arrow_impossibility_card [Fintype V] [Nonempty V] [Fintype A]
    (hA : 3 ≤ Fintype.card A) (F : SWF V A) :
    ¬ (Unanimity F ∧ IIA F ∧ ∀ i : V, ¬ IsDictator F i) :=
  arrow_impossibility (threeAlternatives_of_three_le_card hA) F

/-! ### Consistency of the conditions

The three conditions of Arrow's theorem are not jointly contradictory as such: a dictatorship
does satisfy unanimity and independence of irrelevant alternatives.  It is exactly
non-dictatorship that has to fail. -/

/-- The social welfare function that always copies voter `i`'s ranking. -/
def dictatorship (i : V) : SWF V A := fun P => (P i).toPref

theorem dictatorship_unanimity (i : V) : Unanimity (dictatorship (A := A) i) :=
  fun _ _ _ h => h i

theorem dictatorship_iia (i : V) : IIA (dictatorship (A := A) i) :=
  fun _ _ _ _ h => h i

theorem dictatorship_isDictator (i : V) : IsDictator (dictatorship (A := A) i) i :=
  fun _ _ _ h => h

end Frontier

