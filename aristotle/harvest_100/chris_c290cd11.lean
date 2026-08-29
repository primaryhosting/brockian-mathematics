/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment rather than a `/-!` module docstring, since Lean 4
-- requires `import` commands to precede every command, including module docstrings.)

import Mathlib

set_option maxHeartbeats 1000000

namespace Frontier

/-! ## Preferences

A *preference* on a type of alternatives `A` is a linear (total) order on `A`, presented as a
bundled relation.  This is the classical "ranked ballot" of social choice theory.
-/

/-- A ranking of the alternatives `A`: a total, transitive, antisymmetric relation. -/
structure Pref (A : Type*) where
  /-- The weak preference relation: `rel a b` means `a` is ranked at least as high as `b`. -/
  rel : A → A → Prop
  total' : ∀ a b, rel a b ∨ rel b a
  trans' : ∀ {a b c}, rel a b → rel b c → rel a c
  antisymm' : ∀ {a b}, rel a b → rel b a → a = b

namespace Pref

variable {A : Type*}

/-- Strict preference: `a` is ranked strictly above `b`. -/
def lt (p : Pref A) (a b : A) : Prop := p.rel a b ∧ a ≠ b

lemma rel_refl (p : Pref A) (a : A) : p.rel a a := by
  rcases p.total' a a with h | h <;> exact h

lemma lt_iff (p : Pref A) (a b : A) : p.lt a b ↔ ¬ p.rel b a := by
  constructor
  · rintro ⟨h1, h2⟩ h3
    exact h2 (p.antisymm' h1 h3)
  · intro h
    refine ⟨?_, ?_⟩
    · rcases p.total' a b with h1 | h1
      · exact h1
      · exact absurd h1 h
    · rintro rfl
      exact h (p.rel_refl a)

lemma rel_of_not_lt {p : Pref A} {a b : A} (h : ¬ p.lt b a) : p.rel a b := by
  by_contra hc
  exact h ((p.lt_iff b a).2 hc)

lemma not_lt_of_lt {p : Pref A} {a b : A} (h : p.lt a b) : ¬ p.lt b a := by
  rw [lt_iff]
  intro hc
  exact hc h.1

lemma lt_of_lt_of_rel {p : Pref A} {a b c : A} (h1 : p.lt a b) (h2 : p.rel b c) : p.lt a c := by
  rw [lt_iff] at h1 ⊢
  intro hc
  exact h1 (p.trans' h2 hc)

lemma lt_trans' {p : Pref A} {a b c : A} (h1 : p.lt a b) (h2 : p.lt b c) : p.lt a c :=
  lt_of_lt_of_rel h1 h2.1

end Pref

/-! ## Constructions of preferences -/

section Constructions

variable {A : Type*} [LinearOrder A]

/-- The ranking induced by an integer "score" function (lower score = ranked higher), with ties
broken by a fixed background linear order. -/
def keyPref (key : A → ℤ) : Pref A where
  rel x y := key x < key y ∨ (key x = key y ∧ x ≤ y)
  total' := by
    intro a b
    rcases lt_trichotomy (key a) (key b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total a b with h2 | h2
      · exact Or.inl (Or.inr ⟨h, h2⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h2⟩)
    · exact Or.inr (Or.inl h)
  trans' := by
    rintro a b c (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
    · exact Or.inl (lt_trans h1 h2)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, le_trans h1' h2'⟩
  antisymm' := by
    rintro a b (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
    · omega
    · omega
    · omega
    · exact le_antisymm h1' h2'

lemma keyPref_lt {key : A → ℤ} {x y : A} (h : key x < key y) : (keyPref key).lt x y := by
  rw [Pref.lt_iff]
  rintro (h1 | ⟨h1, -⟩) <;> omega

open Classical in
/-- The score function putting `a` first, `b` second, `c` third and everything else last. -/
noncomputable def key3 (a b c : A) : A → ℤ :=
  fun t => if t = a then 0 else if t = b then 1 else if t = c then 2 else 3

/-- The ranking `a ≻ b ≻ c ≻ (everything else)`. -/
noncomputable def pref3 (a b c : A) : Pref A := keyPref (key3 a b c)

lemma pref3_lt_of_key {a b c x y : A} (h : key3 a b c x < key3 a b c y) : (pref3 a b c).lt x y :=
  keyPref_lt h

/-- Move the alternative `z` to the top of the ranking `p`, keeping everything else unchanged. -/
def topPref (z : A) (p : Pref A) : Pref A where
  rel x y := x = z ∨ (y ≠ z ∧ p.rel x y)
  total' := by
    intro x y
    by_cases hx : x = z
    · exact Or.inl (Or.inl hx)
    by_cases hy : y = z
    · exact Or.inr (Or.inl hy)
    rcases p.total' x y with h | h
    · exact Or.inl (Or.inr ⟨hy, h⟩)
    · exact Or.inr (Or.inr ⟨hx, h⟩)
  trans' := by
    rintro x y w (rfl | ⟨hy, hxy⟩) h2
    · exact Or.inl rfl
    · rcases h2 with rfl | ⟨hw, hyw⟩
      · exact absurd rfl hy
      · exact Or.inr ⟨hw, p.trans' hxy hyw⟩
  antisymm' := by
    rintro x y (rfl | ⟨hy, hxy⟩) h2
    · rcases h2 with rfl | ⟨hx, -⟩
      · rfl
      · exact absurd rfl hx
    · rcases h2 with rfl | ⟨-, hyx⟩
      · exact absurd rfl hy
      · exact p.antisymm' hxy hyx

lemma topPref_lt_top {z : A} {p : Pref A} {x : A} (hx : x ≠ z) : (topPref z p).lt z x := by
  rw [Pref.lt_iff]
  rintro (rfl | ⟨h, -⟩)
  · exact hx rfl
  · exact h rfl

lemma topPref_lt_iff {z : A} {p : Pref A} {x y : A} (hx : x ≠ z) (hy : y ≠ z) :
    (topPref z p).lt x y ↔ p.lt x y := by
  rw [Pref.lt_iff, Pref.lt_iff]
  constructor
  · intro h h2
    exact h (Or.inr ⟨hx, h2⟩)
  · rintro h (rfl | ⟨-, h2⟩)
    · exact hy rfl
    · exact h h2

end Constructions

/-! ## Social welfare functions and Arrow's axioms -/

section Axioms

variable {V A : Type*}

/-- A social welfare function aggregates a profile of individual rankings into a social ranking. -/
abbrev SWF (V A : Type*) := (V → Pref A) → Pref A

/-- Unanimity (weak Pareto): if every voter strictly prefers `a` to `b`, so does society. -/
def Unanimous (F : SWF V A) : Prop :=
  ∀ (P : V → Pref A) (a b : A), (∀ i, (P i).lt a b) → (F P).lt a b

/-- Independence of irrelevant alternatives: the social ranking of `a` versus `b` depends only
on the individual rankings of `a` versus `b`. -/
def IIA (F : SWF V A) : Prop :=
  ∀ (P Q : V → Pref A) (a b : A), (∀ i, ((P i).lt a b ↔ (Q i).lt a b)) →
    ((F P).lt a b ↔ (F Q).lt a b)

/-- Voter `i` is a dictator: society always follows `i`'s strict preferences. -/
def IsDictator (F : SWF V A) (i : V) : Prop :=
  ∀ (P : V → Pref A) (a b : A), (P i).lt a b → (F P).lt a b

end Axioms

/-! ## Decisive coalitions -/

section Decisive

variable {V A : Type*} (F : SWF V A)

/-- The coalition `S` is *almost decisive* for the ordered pair `(a, b)`: whenever the members of
`S` prefer `a` to `b` and everyone else prefers `b` to `a`, society prefers `a` to `b`. -/
def AlmostDecisive (S : Finset V) (a b : A) : Prop :=
  ∀ P : V → Pref A, (∀ i ∈ S, (P i).lt a b) → (∀ i ∉ S, (P i).lt b a) → (F P).lt a b

/-- The coalition `S` is *decisive*: whenever its members prefer `x` to `y`, so does society,
no matter what the other voters think. -/
def Decisive (S : Finset V) : Prop :=
  ∀ (x y : A), x ≠ y → ∀ P : V → Pref A, (∀ i ∈ S, (P i).lt x y) → (F P).lt x y

end Decisive

section Expansion

variable {V A : Type*} [LinearOrder A] [DecidableEq V] {F : SWF V A}
  (hu : Unanimous F) (hi : IIA F)

include hu hi

/-- Field expansion, part 1: almost decisive for `(a,b)` implies almost decisive for `(a,c)`. -/
lemma ad_expand_right {S : Finset V} {a b c : A} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (h : AlmostDecisive F S a b) : AlmostDecisive F S a c := by
  classical
  set Q : V → Pref A := fun i => if i ∈ S then pref3 a b c else pref3 b c a with hQ
  have hQin : ∀ i ∈ S, Q i = pref3 a b c := by intro i hiS; simp [hQ, hiS]
  have hQout : ∀ i ∉ S, Q i = pref3 b c a := by intro i hiS; simp [hQ, hiS]
  -- society prefers `a` to `b`
  have hab' : (F Q).lt a b := by
    refine h Q (fun i hiS => ?_) (fun i hiS => ?_)
    · rw [hQin i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])
    · rw [hQout i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])
  -- society prefers `b` to `c` by unanimity
  have hbc' : (F Q).lt b c := by
    refine hu Q b c (fun i => ?_)
    by_cases hiS : i ∈ S
    · rw [hQin i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])
    · rw [hQout i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])
  have hac' : (F Q).lt a c := Pref.lt_trans' hab' hbc'
  intro P hin hout
  refine (hi P Q a c (fun i => ?_)).2 hac'
  by_cases hiS : i ∈ S
  · rw [hQin i hiS]
    exact iff_of_true (hin i hiS)
      (pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm]))
  · rw [hQout i hiS]
    refine iff_of_false (Pref.not_lt_of_lt (hout i hiS)) (Pref.not_lt_of_lt ?_)
    exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])

/-- Field expansion, part 2: almost decisive for `(a,b)` implies almost decisive for `(c,b)`. -/
lemma ad_expand_left {S : Finset V} {a b c : A} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (h : AlmostDecisive F S a b) : AlmostDecisive F S c b := by
  classical
  set Q : V → Pref A := fun i => if i ∈ S then pref3 c a b else pref3 b c a with hQ
  have hQin : ∀ i ∈ S, Q i = pref3 c a b := by intro i hiS; simp [hQ, hiS]
  have hQout : ∀ i ∉ S, Q i = pref3 b c a := by intro i hiS; simp [hQ, hiS]
  have hab' : (F Q).lt a b := by
    refine h Q (fun i hiS => ?_) (fun i hiS => ?_)
    · rw [hQin i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])
    · rw [hQout i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])
  have hca' : (F Q).lt c a := by
    refine hu Q c a (fun i => ?_)
    by_cases hiS : i ∈ S
    · rw [hQin i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])
    · rw [hQout i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])
  have hcb' : (F Q).lt c b := Pref.lt_trans' hca' hab'
  intro P hin hout
  refine (hi P Q c b (fun i => ?_)).2 hcb'
  by_cases hiS : i ∈ S
  · rw [hQin i hiS]
    exact iff_of_true (hin i hiS)
      (pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm]))
  · rw [hQout i hiS]
    refine iff_of_false (Pref.not_lt_of_lt (hout i hiS)) (Pref.not_lt_of_lt ?_)
    exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])

/-- Almost decisiveness is symmetric in the pair, given a third alternative. -/
lemma ad_swap {S : Finset V} {a b : A} (hab : a ≠ b) (c : A) (hca : c ≠ a) (hcb : c ≠ b)
    (h : AlmostDecisive F S a b) : AlmostDecisive F S b a := by
  have h1 : AlmostDecisive F S c b := ad_expand_left hu hi hab hca hcb h
  have h2 : AlmostDecisive F S c a := ad_expand_right hu hi hcb (Ne.symm hca) hab h1
  exact ad_expand_left hu hi hca (Ne.symm hcb) (Ne.symm hab) h2

/-- Almost decisiveness for one pair implies almost decisiveness for every pair. -/
lemma ad_all (hthree : ∀ x y : A, ∃ z : A, z ≠ x ∧ z ≠ y) {S : Finset V} {p q : A} (hpq : p ≠ q)
    (h : AlmostDecisive F S p q) : ∀ x y : A, x ≠ y → AlmostDecisive F S x y := by
  obtain ⟨t, htp, htq⟩ := hthree p q
  have hqp : AlmostDecisive F S q p := ad_swap hu hi hpq t htp htq h
  intro x y hxy
  by_cases hxp : x = p
  · subst hxp
    by_cases hyq : y = q
    · subst hyq; exact h
    · exact ad_expand_right hu hi hpq (Ne.symm hxy) hyq h
  · by_cases hxq : x = q
    · subst hxq
      by_cases hyp : y = p
      · subst hyp; exact hqp
      · exact ad_expand_right hu hi (Ne.symm hpq) (Ne.symm hxy) hyp hqp
    · by_cases hyq : y = q
      · subst hyq; exact ad_expand_left hu hi hpq hxp hxy h
      · by_cases hyp : y = p
        · subst hyp
          exact ad_expand_left hu hi (Ne.symm hpq) hxq hxy hqp
        · have h1 : AlmostDecisive F S p y := ad_expand_right hu hi hpq hyp hyq h
          exact ad_expand_left hu hi (Ne.symm hyp) hxp hxy h1

/-- Almost decisiveness for a single pair upgrades to full decisiveness. -/
lemma decisive_of_ad (hthree : ∀ x y : A, ∃ z : A, z ≠ x ∧ z ≠ y) {S : Finset V} {p q : A}
    (hpq : p ≠ q) (h : AlmostDecisive F S p q) : Decisive F S := by
  classical
  have hAD := ad_all hu hi hthree hpq h
  intro x y hxy P hin
  obtain ⟨z, hzx, hzy⟩ := hthree x y
  set Q : V → Pref A := fun i => if i ∈ S then pref3 x z y else topPref z (P i) with hQ
  have hQin : ∀ i ∈ S, Q i = pref3 x z y := by intro i hiS; simp [hQ, hiS]
  have hQout : ∀ i ∉ S, Q i = topPref z (P i) := by intro i hiS; simp [hQ, hiS]
  have hxz' : (F Q).lt x z := by
    refine hAD x z (Ne.symm hzx) Q (fun i hiS => ?_) (fun i hiS => ?_)
    · rw [hQin i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hxy, hxy.symm, hzx, hzx.symm, hzy, hzy.symm])
    · rw [hQout i hiS]
      exact topPref_lt_top (Ne.symm hzx)
  have hzy' : (F Q).lt z y := by
    refine hu Q z y (fun i => ?_)
    by_cases hiS : i ∈ S
    · rw [hQin i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hxy, hxy.symm, hzx, hzx.symm, hzy, hzy.symm])
    · rw [hQout i hiS]
      exact topPref_lt_top (Ne.symm hzy)
  have hxy' : (F Q).lt x y := Pref.lt_trans' hxz' hzy'
  refine (hi P Q x y (fun i => ?_)).2 hxy'
  by_cases hiS : i ∈ S
  · rw [hQin i hiS]
    exact iff_of_true (hin i hiS)
      (pref3_lt_of_key (by norm_num [key3, hxy, hxy.symm, hzx, hzx.symm, hzy, hzy.symm]))
  · rw [hQout i hiS]
    exact (topPref_lt_iff (Ne.symm hzx) (Ne.symm hzy)).symm

omit [LinearOrder A] [DecidableEq V] hi in
/-- The whole electorate is decisive, by unanimity. -/
lemma decisive_univ [Fintype V] : Decisive F (Finset.univ : Finset V) := by
  intro x y _ P hin
  exact hu P x y (fun i => hin i (Finset.mem_univ i))

end Expansion

/-! ## Arrow's theorem -/

section Main

variable {V A : Type*} [Fintype V]

/-- With three distinct alternatives available, for any two alternatives there is a third one
different from both. -/
lemma exists_third (hthree : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z) :
    ∀ x y : A, ∃ z : A, z ≠ x ∧ z ≠ y := by
  obtain ⟨p, q, r, hpq, hpr, hqr⟩ := hthree
  intro x y
  by_contra hcon
  push_neg at hcon
  have key : ∀ z : A, z = x ∨ z = y := by
    intro z
    rcases eq_or_ne z x with h | h
    · exact Or.inl h
    · exact Or.inr (hcon z h)
  rcases key p with hp | hp <;> rcases key q with hq | hq <;> rcases key r with hr | hr
  · exact hpq (hp.trans hq.symm)
  · exact hpq (hp.trans hq.symm)
  · exact hpr (hp.trans hr.symm)
  · exact hqr (hq.trans hr.symm)
  · exact hqr (hq.trans hr.symm)
  · exact hpr (hp.trans hr.symm)
  · exact hpq (hp.trans hq.symm)
  · exact hpq (hp.trans hq.symm)

/-- **Arrow's impossibility theorem** (dictator form): with at least three alternatives and
finitely many voters, every unanimous social welfare function satisfying IIA has a dictator. -/
theorem exists_dictator (F : SWF V A) (hthree : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z)
    (hu : Unanimous F) (hi : IIA F) : ∃ i : V, IsDictator F i := by
  classical
  letI : LinearOrder A := IsWellOrder.linearOrder (WellOrderingRel (α := A))
  have h3 : ∀ x y : A, ∃ z : A, z ≠ x ∧ z ≠ y := exists_third hthree
  obtain ⟨p, q, r, hpq, hpr, hqr⟩ := hthree
  -- a decisive coalition of minimal size
  have hex : ∃ n, ∃ S : Finset V, S.card = n ∧ Decisive F S :=
    ⟨_, Finset.univ, rfl, decisive_univ hu⟩
  obtain ⟨S, hScard, hS⟩ := Nat.find_spec hex
  have hmin : ∀ T : Finset V, Decisive F T → Nat.find hex ≤ T.card :=
    fun T hT => Nat.find_min' hex ⟨T, rfl, hT⟩
  -- the minimal decisive coalition is nonempty
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exfalso
      have h1 := hS p q hpq (fun _ => pref3 p q r) (by simp)
      have h2 := hS q p (Ne.symm hpq) (fun _ => pref3 p q r) (by simp)
      exact Pref.not_lt_of_lt h1 h2
    · exact hne
  obtain ⟨i, hiS⟩ := hSne
  -- the minimal decisive coalition is a singleton
  have hcard1 : S.card ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    set S' : Finset V := S.erase i with hS'
    have hS'card : S'.card < S.card := Finset.card_erase_lt_of_mem hiS
    set Q : V → Pref A :=
      fun j => if j = i then pref3 p q r else if j ∈ S then pref3 r p q else pref3 q r p with hQ
    have hQi : Q i = pref3 p q r := by simp [hQ]
    have hQmid : ∀ j ∈ S', Q j = pref3 r p q := by
      intro j hj
      have h1 : j ≠ i := Finset.ne_of_mem_erase hj
      have h2 : j ∈ S := Finset.mem_of_mem_erase hj
      simp [hQ, h1, h2]
    have hQout : ∀ j ∉ S, Q j = pref3 q r p := by
      intro j hj
      have h1 : j ≠ i := by rintro rfl; exact hj hiS
      simp [hQ, h1, hj]
    -- society ranks `p` above `q`, since `S` is decisive
    have hpq' : (F Q).lt p q := by
      refine hS p q hpq Q (fun j hjS => ?_)
      by_cases hji : j = i
      · subst hji
        rw [hQi]
        exact pref3_lt_of_key (by norm_num [key3, hpq, hpq.symm, hpr, hpr.symm, hqr, hqr.symm])
      · rw [hQmid j (Finset.mem_erase.2 ⟨hji, hjS⟩)]
        exact pref3_lt_of_key (by norm_num [key3, hpq, hpq.symm, hpr, hpr.symm, hqr, hqr.symm])
    -- society cannot rank `r` above `q`, else `S'` would be decisive
    have hnrq : ¬ (F Q).lt r q := by
      intro hrq
      have hAD : AlmostDecisive F S' r q := by
        intro P hin hout
        refine (hi P Q r q (fun j => ?_)).2 hrq
        by_cases hjS' : j ∈ S'
        · rw [hQmid j hjS']
          exact iff_of_true (hin j hjS')
            (pref3_lt_of_key (by norm_num [key3, hpq, hpq.symm, hpr, hpr.symm, hqr, hqr.symm]))
        · refine iff_of_false (Pref.not_lt_of_lt (hout j hjS')) (Pref.not_lt_of_lt ?_)
          by_cases hji : j = i
          · subst hji
            rw [hQi]
            exact pref3_lt_of_key (by norm_num [key3, hpq, hpq.symm, hpr, hpr.symm, hqr, hqr.symm])
          · have hjS : j ∉ S := by
              intro hjS
              exact hjS' (Finset.mem_erase.2 ⟨hji, hjS⟩)
            rw [hQout j hjS]
            exact pref3_lt_of_key (by norm_num [key3, hpq, hpq.symm, hpr, hpr.symm, hqr, hqr.symm])
      have : Decisive F S' := decisive_of_ad hu hi h3 (Ne.symm hqr) hAD
      have := hmin S' this
      omega
    -- hence society ranks `p` above `r`
    have hpr' : (F Q).lt p r := Pref.lt_of_lt_of_rel hpq' (Pref.rel_of_not_lt hnrq)
    -- so `{i}` is almost decisive for `(p, r)`, hence decisive
    have hADi : AlmostDecisive F ({i} : Finset V) p r := by
      intro P hin hout
      refine (hi P Q p r (fun j => ?_)).2 hpr'
      by_cases hji : j = i
      · subst hji
        rw [hQi]
        exact iff_of_true (hin j (Finset.mem_singleton_self j))
          (pref3_lt_of_key (by norm_num [key3, hpq, hpq.symm, hpr, hpr.symm, hqr, hqr.symm]))
      · have hjns : j ∉ ({i} : Finset V) := by simpa using hji
        refine iff_of_false (Pref.not_lt_of_lt (hout j hjns)) (Pref.not_lt_of_lt ?_)
        by_cases hjS : j ∈ S
        · rw [hQmid j (Finset.mem_erase.2 ⟨hji, hjS⟩)]
          exact pref3_lt_of_key (by norm_num [key3, hpq, hpq.symm, hpr, hpr.symm, hqr, hqr.symm])
        · rw [hQout j hjS]
          exact pref3_lt_of_key (by norm_num [key3, hpq, hpq.symm, hpr, hpr.symm, hqr, hqr.symm])
    have hdi : Decisive F ({i} : Finset V) := decisive_of_ad hu hi h3 hpr hADi
    have := hmin _ hdi
    rw [Finset.card_singleton] at this
    omega
  -- the unique member of `S` is a dictator
  refine ⟨i, ?_⟩
  intro P x y hxy
  refine hS x y hxy.2 P (fun j hjS => ?_)
  rw [Finset.card_le_one.mp hcard1 j hjS i hiS]
  exact hxy

/-- **Arrow's impossibility theorem.**  For at least three alternatives and a finite electorate,
no social welfare function is simultaneously unanimous, independent of irrelevant alternatives,
and non-dictatorial. -/
theorem arrow_impossibility (F : SWF V A) (hthree : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z) :
    ¬ (Unanimous F ∧ IIA F ∧ ∀ i : V, ¬ IsDictator F i) := by
  rintro ⟨hu, hi, hnd⟩
  obtain ⟨i, hdict⟩ := exists_dictator F hthree hu hi
  exact hnd i hdict

/-! ### Consistency check

The axioms are not vacuously unsatisfiable: a dictatorship is unanimous and satisfies IIA.
The content of Arrow's theorem is exactly that these are the only such rules. -/

omit [Fintype V] in
/-- The rule "always copy voter `i₀`'s ballot" is unanimous. -/
lemma dictatorship_unanimous (i₀ : V) : Unanimous (fun P : V → Pref A => P i₀) :=
  fun _ _ _ h => h i₀

omit [Fintype V] in
/-- The rule "always copy voter `i₀`'s ballot" satisfies IIA. -/
lemma dictatorship_iia (i₀ : V) : IIA (fun P : V → Pref A => P i₀) :=
  fun _ _ _ _ h => h i₀

omit [Fintype V] in
/-- The rule "always copy voter `i₀`'s ballot" is dictatorial, with dictator `i₀`. -/
lemma dictatorship_isDictator (i₀ : V) : IsDictator (fun P : V → Pref A => P i₀) i₀ :=
  fun _ _ _ h => h

end Main

end Frontier

