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
