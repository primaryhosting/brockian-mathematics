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
