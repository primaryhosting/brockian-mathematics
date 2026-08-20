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
