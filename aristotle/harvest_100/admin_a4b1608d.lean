import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Rankings -/

/-- A strict linear ranking (irreflexive, transitive, total) of the alternatives `A`.
`R.rel a b` means "`a` is strictly preferred to `b`". -/
structure Ranking (A : Type*) where
  /-- The strict preference relation. -/
  rel : A → A → Prop
  rel_trans : ∀ {a b c : A}, rel a b → rel b c → rel a c
  rel_irrefl : ∀ a : A, ¬ rel a a
  rel_total : ∀ a b : A, a ≠ b → rel a b ∨ rel b a

namespace Ranking

variable {A : Type*}

theorem asymm (R : Ranking A) {a b : A} (h : R.rel a b) : ¬ R.rel b a :=
  fun h' => R.rel_irrefl a (R.rel_trans h h')

theorem rel_of_not_rel (R : Ranking A) {a b : A} (hab : a ≠ b) (h : ¬ R.rel a b) : R.rel b a :=
  (R.rel_total a b hab).resolve_left h

end Ranking

/-- `b` is the most preferred alternative of the ranking `R`. -/
def IsTopOf {A : Type*} (b : A) (R : Ranking A) : Prop := ∀ x, x ≠ b → R.rel b x

/-- `b` is the least preferred alternative of the ranking `R`. -/
def IsBotOf {A : Type*} (b : A) (R : Ranking A) : Prop := ∀ x, x ≠ b → R.rel x b

/-! ## Building rankings from scores -/

/-- The strict ranking induced by a "score" function (a lower score means more preferred),
with ties broken by a fixed well-ordering of the alternatives.  This lets us build a ranking
realizing any prescribed preferences among finitely many designated alternatives. -/
noncomputable def scoreRanking {A : Type*} (s : A → ℕ) : Ranking A where
  rel a b := s a < s b ∨ (s a = s b ∧ WellOrderingRel a b)
  rel_trans := by
    rintro a b c (h1 | ⟨h1, w1⟩) (h2 | ⟨h2, w2⟩)
    · exact Or.inl (lt_trans h1 h2)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, _root_.trans w1 w2⟩
  rel_irrefl := by
    rintro a (h | ⟨-, w⟩)
    · exact lt_irrefl _ h
    · exact irrefl_of WellOrderingRel a w
  rel_total := by
    intro a b hab
    rcases lt_trichotomy (s a) (s b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases trichotomous_of WellOrderingRel a b with w | w | w
      · exact Or.inl (Or.inr ⟨h, w⟩)
      · exact absurd w hab
      · exact Or.inr (Or.inr ⟨h.symm, w⟩)
    · exact Or.inr (Or.inl h)

theorem scoreRanking_rel {A : Type*} {s : A → ℕ} {x y : A} (h : s x < s y) :
    (scoreRanking s).rel x y := Or.inl h

theorem scoreRanking_not_rel {A : Type*} {s : A → ℕ} {x y : A} (h : s y < s x) :
    ¬ (scoreRanking s).rel x y := by
  rintro (h' | ⟨h', -⟩) <;> omega

/-! ## Social welfare functions and Arrow's conditions -/

/-- A social welfare function: it aggregates a profile of individual rankings (one per voter
in `V`) into a single social ranking of the alternatives `A`. -/
abbrev SWF (V A : Type*) := (V → Ranking A) → Ranking A

variable {A V : Type*}

/-- Unanimity (the weak Pareto condition): if every voter strictly prefers `a` to `b`,
so does society. -/
def Unanimity (F : SWF V A) : Prop :=
  ∀ (P : V → Ranking A) (a b : A), (∀ v, (P v).rel a b) → (F P).rel a b

/-- Independence of irrelevant alternatives: the social preference between `a` and `b`
depends only on the individual preferences between `a` and `b`. -/
def IIA (F : SWF V A) : Prop :=
  ∀ (P Q : V → Ranking A) (a b : A), (∀ v, ((P v).rel a b ↔ (Q v).rel a b)) →
    ((F P).rel a b ↔ (F Q).rel a b)

/-- `v` is a dictator: society always follows `v`'s strict preferences. -/
def Dictator (F : SWF V A) (v : V) : Prop :=
  ∀ (P : V → Ranking A) (a b : A), (P v).rel a b → (F P).rel a b

/-- `v` is decisive for the ordered pair `(a, b)`: whenever `v` prefers `a` to `b`, so does
society, regardless of everyone else's preferences. -/
def Decisive (F : SWF V A) (v : V) (a b : A) : Prop :=
  ∀ (P : V → Ranking A), (P v).rel a b → (F P).rel a b

/-! ## The extremal lemma -/

/-- If an alternative `b` is at the top or at the bottom of every voter's ranking, then it is
at the top or at the bottom of the social ranking. -/
theorem extremal_lemma {F : SWF V A} (hU : Unanimity F) (hI : IIA F) (b : A)
    (P : V → Ranking A) (hP : ∀ v, IsTopOf b (P v) ∨ IsBotOf b (P v)) :
    IsTopOf b (F P) ∨ IsBotOf b (F P) := by
  classical
  by_contra hcon
  simp only [IsTopOf, IsBotOf, not_or] at hcon
  obtain ⟨hnt, hnb⟩ := hcon
  push_neg at hnt hnb
  obtain ⟨a, hab, hna⟩ := hnt
  obtain ⟨c, hcb, hnc⟩ := hnb
  have hFa : (F P).rel a b := (F P).rel_of_not_rel (Ne.symm hab) hna
  have hFc : (F P).rel b c := (F P).rel_of_not_rel hcb hnc
  have hac : a ≠ c := by
    rintro rfl
    exact (F P).rel_irrefl a ((F P).rel_trans hFa hFc)
  -- Build a profile `Q` where `b` keeps its extremal position for each voter, but everyone
  -- ranks `c` above `a`.
  obtain ⟨s, hs⟩ : ∃ s : V → A → ℕ, s = fun v x =>
      if x = b then (if IsTopOf b (P v) then 0 else 4)
      else if x = c then 1 else if x = a then 2 else 3 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : V → Ranking A, Q = fun v => scoreRanking (s v) := ⟨_, rfl⟩
  have hnotTop : ∀ v, IsBotOf b (P v) → ¬ IsTopOf b (P v) := fun v hb ht =>
    (P v).asymm (ht a hab) (hb a hab)
  have hsb : ∀ v, s v b = (if IsTopOf b (P v) then 0 else 4) := by intro v; simp [hs]
  have hsa : ∀ v, s v a = 2 := by intro v; simp [hs, hab, hac]
  have hsc : ∀ v, s v c = 1 := by intro v; simp [hs, hcb]
  -- everyone prefers `c` to `a` in `Q`
  have hca : ∀ v, (Q v).rel c a := by
    intro v
    simp only [hQ]
    exact scoreRanking_rel (by rw [hsa, hsc]; omega)
  -- the `(a, b)` comparisons agree with `P`
  have hmab : ∀ v, ((Q v).rel a b ↔ (P v).rel a b) := by
    intro v
    rcases hP v with h | h
    · refine iff_of_false ?_ ?_
      · simp only [hQ]
        exact scoreRanking_not_rel (by rw [hsa, hsb, if_pos h]; omega)
      · exact (P v).asymm (h a hab)
    · refine iff_of_true ?_ (h a hab)
      simp only [hQ]
      exact scoreRanking_rel (by rw [hsa, hsb, if_neg (hnotTop v h)]; omega)
  -- the `(b, c)` comparisons agree with `P`
  have hmbc : ∀ v, ((Q v).rel b c ↔ (P v).rel b c) := by
    intro v
    rcases hP v with h | h
    · refine iff_of_true ?_ (h c hcb)
      simp only [hQ]
      exact scoreRanking_rel (by rw [hsc, hsb, if_pos h]; omega)
    · refine iff_of_false ?_ ?_
      · simp only [hQ]
        exact scoreRanking_not_rel (by rw [hsc, hsb, if_neg (hnotTop v h)]; omega)
      · exact (P v).asymm (h c hcb)
  have h1 : (F Q).rel a b := (hI Q P a b hmab).mpr hFa
  have h2 : (F Q).rel b c := (hI Q P b c hmbc).mpr hFc
  have h3 : (F Q).rel c a := hU Q c a hca
  exact (F Q).rel_irrefl a ((F Q).rel_trans ((F Q).rel_trans h1 h2) h3)

/-! ## Field expansion: spreading decisiveness from one pair to all pairs -/

/-- Extending decisiveness on the right: if `v` is decisive for `(a, c)`, then `v` is decisive
for `(a, d)` for every `d ≠ a`. -/
theorem decisive_right {F : SWF V A} (hU : Unanimity F) (hI : IIA F) {v : V} {a c : A}
    (hac : a ≠ c) (hac' : Decisive F v a c) {d : A} (hda : d ≠ a) : Decisive F v a d := by
  classical
  by_cases hdc : d = c
  · subst hdc; exact hac'
  intro P hP
  obtain ⟨s, hs⟩ : ∃ s : V → A → ℕ, s = fun i y =>
      if i = v then (if y = a then 0 else if y = c then 1 else if y = d then 2 else 3)
      else (if y = c then 0 else if y = a then (if (P i).rel a d then 1 else 3)
            else if y = d then (if (P i).rel a d then 3 else 1) else 2) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : V → Ranking A, Q = fun i => scoreRanking (s i) := ⟨_, rfl⟩
  have hva : s v a = 0 := by simp [hs]
  have hvc : s v c = 1 := by simp [hs, Ne.symm hac]
  have hvd : s v d = 2 := by simp [hs, hda, hdc]
  have hic : ∀ i, i ≠ v → s i c = 0 := by intro i hi; simp [hs, hi]
  have hia : ∀ i, i ≠ v → s i a = (if (P i).rel a d then 1 else 3) := by
    intro i hi; simp [hs, hi, hac]
  have hid : ∀ i, i ≠ v → s i d = (if (P i).rel a d then 3 else 1) := by
    intro i hi; simp [hs, hi, hdc, hda]
  have hQac : (Q v).rel a c := by
    simp only [hQ]; exact scoreRanking_rel (by rw [hva, hvc]; omega)
  have hQcd : ∀ i, (Q i).rel c d := by
    intro i
    by_cases hi : i = v
    · subst hi; simp only [hQ]; exact scoreRanking_rel (by rw [hvc, hvd]; omega)
    · simp only [hQ]
      exact scoreRanking_rel (by rw [hic i hi, hid i hi]; split_ifs <;> omega)
  have hQad : ∀ i, ((Q i).rel a d ↔ (P i).rel a d) := by
    intro i
    by_cases hi : i = v
    · subst hi
      exact iff_of_true (by simp only [hQ]; exact scoreRanking_rel (by rw [hva, hvd]; omega)) hP
    · by_cases hp : (P i).rel a d
      · refine iff_of_true ?_ hp
        simp only [hQ]
        exact scoreRanking_rel (by rw [hia i hi, hid i hi, if_pos hp, if_pos hp]; omega)
      · refine iff_of_false ?_ hp
        simp only [hQ]
        exact scoreRanking_not_rel (by rw [hia i hi, hid i hi, if_neg hp, if_neg hp]; omega)
  exact (hI P Q a d (fun i => (hQad i).symm)).mpr
    ((F Q).rel_trans (hac' Q hQac) (hU Q c d hQcd))

/-- Extending decisiveness on the left: if `v` is decisive for `(a, d)`, then `v` is decisive
for `(x, d)` for every `x ≠ d`. -/
theorem decisive_left {F : SWF V A} (hU : Unanimity F) (hI : IIA F) {v : V} {a d : A}
    (had : a ≠ d) (had' : Decisive F v a d) {x : A} (hxd : x ≠ d) : Decisive F v x d := by
  classical
  by_cases hxa : x = a
  · subst hxa; exact had'
  intro P hP
  obtain ⟨s, hs⟩ : ∃ s : V → A → ℕ, s = fun i y =>
      if y = x then (if i = v ∨ (P i).rel x d then 0 else 1)
      else if y = a then (if i = v ∨ (P i).rel x d then 1 else 2)
      else if y = d then (if i = v ∨ (P i).rel x d then 2 else 0) else 3 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : V → Ranking A, Q = fun i => scoreRanking (s i) := ⟨_, rfl⟩
  have hsx : ∀ i, s i x = (if i = v ∨ (P i).rel x d then 0 else 1) := by intro i; simp [hs]
  have hsa : ∀ i, s i a = (if i = v ∨ (P i).rel x d then 1 else 2) := by
    intro i; simp [hs, Ne.symm hxa]
  have hsd : ∀ i, s i d = (if i = v ∨ (P i).rel x d then 2 else 0) := by
    intro i; simp [hs, Ne.symm hxd, Ne.symm had]
  have hQxa : ∀ i, (Q i).rel x a := by
    intro i
    simp only [hQ]
    exact scoreRanking_rel (by rw [hsx i, hsa i]; split_ifs <;> omega)
  have hQad : (Q v).rel a d := by
    simp only [hQ]
    exact scoreRanking_rel (by rw [hsa v, hsd v, if_pos (Or.inl rfl), if_pos (Or.inl rfl)]; omega)
  have hQxd : ∀ i, ((Q i).rel x d ↔ (P i).rel x d) := by
    intro i
    by_cases hi : i = v
    · subst hi
      refine iff_of_true ?_ hP
      simp only [hQ]
      exact scoreRanking_rel (by rw [hsx i, hsd i, if_pos (Or.inl rfl), if_pos (Or.inl rfl)]; omega)
    · by_cases hp : (P i).rel x d
      · refine iff_of_true ?_ hp
        simp only [hQ]
        refine scoreRanking_rel ?_
        rw [hsx i, hsd i, if_pos (Or.inr hp), if_pos (Or.inr hp)]; omega
      · refine iff_of_false ?_ hp
        simp only [hQ]
        refine scoreRanking_not_rel ?_
        rw [hsx i, hsd i, if_neg (by tauto), if_neg (by tauto)]; omega
  exact (hI P Q x d (fun i => (hQxd i).symm)).mpr
    ((F Q).rel_trans (hU Q x a hQxa) (had' Q hQad))

/-- With at least three alternatives, any triple of distinct alternatives lets us avoid any
two given alternatives. -/
theorem exists_ne_two {e₁ e₂ e₃ : A} (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) (p q : A) :
    ∃ z : A, z ≠ p ∧ z ≠ q := by
  rcases eq_or_ne e₁ p with rfl | h1
  · rcases eq_or_ne e₂ q with rfl | h2
    · exact ⟨e₃, Ne.symm h13, Ne.symm h23⟩
    · exact ⟨e₂, Ne.symm h12, h2⟩
  · rcases eq_or_ne e₁ q with rfl | hq
    · rcases eq_or_ne e₂ p with rfl | h2
      · exact ⟨e₃, Ne.symm h23, Ne.symm h13⟩
      · exact ⟨e₂, h2, Ne.symm h12⟩
    · exact ⟨e₁, h1, hq⟩

/-- Field expansion lemma: decisiveness over a single pair implies dictatorship. -/
theorem dictator_of_decisive {F : SWF V A} (hU : Unanimity F) (hI : IIA F) {v : V} {a c : A}
    (hac : a ≠ c) (hac' : Decisive F v a c) {e₁ e₂ e₃ : A}
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) : Dictator F v := by
  have key : ∀ x y : A, x ≠ y → Decisive F v x y := by
    intro x y hxy
    obtain ⟨z, hza, hzx⟩ := exists_ne_two h12 h13 h23 a x
    have d1 : Decisive F v a z := decisive_right hU hI hac hac' hza
    have d2 : Decisive F v x z := decisive_left hU hI (Ne.symm hza) d1 (Ne.symm hzx)
    exact decisive_right hU hI (Ne.symm hzx) d2 (Ne.symm hxy)
  intro P x y hxy
  rcases eq_or_ne x y with rfl | hne
  · exact absurd hxy ((P v).rel_irrefl x)
  · exact key x y hne P hxy

/-! ## The pivotal voter -/

/-- The pivotal voter argument, for voters indexed by `Fin n`: given three distinct
alternatives `a`, `b`, `c`, some voter is decisive for the pair `(a, c)`. -/
theorem exists_decisive_fin {n : ℕ} {A : Type*} {F : SWF (Fin n) A}
    (hU : Unanimity F) (hI : IIA F) {a b c : A} (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c) :
    ∃ v : Fin n, Decisive F v a c := by
  classical
  -- `Pi k` is the profile in which the voters `i < k` rank `b` first and the others rank it last.
  obtain ⟨t, ht⟩ : ∃ t : ℕ → Fin n → A → ℕ, t = fun k i x =>
      if x = b then (if i.val < k then 0 else 2) else 1 := ⟨_, rfl⟩
  obtain ⟨Pi, hPi⟩ : ∃ Pi : ℕ → Fin n → Ranking A, Pi = fun k i => scoreRanking (t k i) := ⟨_, rfl⟩
  have htb : ∀ k (i : Fin n), t k i b = (if i.val < k then 0 else 2) := by
    intro k i; simp [ht]
  have htx : ∀ k (i : Fin n) x, x ≠ b → t k i x = 1 := by intro k i x hx; simp [ht, hx]
  have htop : ∀ k (i : Fin n), i.val < k → IsTopOf b (Pi k i) := by
    intro k i hik x hx
    simp only [hPi]
    exact scoreRanking_rel (by rw [htb, htx k i x hx]; split_ifs; omega)
  have hbot : ∀ k (i : Fin n), ¬ (i.val < k) → IsBotOf b (Pi k i) := by
    intro k i hik x hx
    simp only [hPi]
    exact scoreRanking_rel (by rw [htb, htx k i x hx]; split_ifs; omega)
  have hext : ∀ k, ∀ i : Fin n, IsTopOf b (Pi k i) ∨ IsBotOf b (Pi k i) := by
    intro k i
    by_cases h : i.val < k
    · exact Or.inl (htop k i h)
    · exact Or.inr (hbot k i h)
  have hFtop_n : IsTopOf b (F (Pi n)) := fun x hx => hU _ b x (fun i => htop n i i.isLt x hx)
  have hFbot_0 : IsBotOf b (F (Pi 0)) := fun x hx => hU _ x b (fun i => hbot 0 i (by omega) x hx)
  have hex : ∃ k, IsTopOf b (F (Pi k)) := ⟨n, hFtop_n⟩
  have hk0 : ¬ IsTopOf b (F (Pi 0)) := fun h =>
    (F (Pi 0)).asymm (h a hab) (hFbot_0 a hab)
  have hne0 : Nat.find hex ≠ 0 := fun h => hk0 (h ▸ Nat.find_spec hex)
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hjn : j < n := by
    have h1 : Nat.find hex ≤ n := Nat.find_le hFtop_n
    omega
  have htopk : IsTopOf b (F (Pi (j + 1))) := hj ▸ Nat.find_spec hex
  have hnotj : ¬ IsTopOf b (F (Pi j)) := Nat.find_min hex (by omega)
  have hbotj : IsBotOf b (F (Pi j)) := (extremal_lemma hU hI b (Pi j) (hext j)).resolve_left hnotj
  refine ⟨⟨j, hjn⟩, ?_⟩
  intro P hP
  -- The auxiliary profile `R`: the pivotal voter ranks `a` above `b` above `c`; the earlier
  -- voters keep `b` on top, the later ones keep `b` at the bottom, and everybody else's
  -- `a`-versus-`c` comparison is copied from `P`.
  obtain ⟨s, hs⟩ : ∃ s : Fin n → A → ℕ, s = fun i x =>
      if x = b then (if i.val < j then 0 else if i.val = j then 2 else 4)
      else if x = a then (if i.val = j then 1 else if (P i).rel a c then 1 else 3)
      else if x = c then (if i.val = j then 3 else if (P i).rel a c then 3 else 1)
      else 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Fin n → Ranking A, R = fun i => scoreRanking (s i) := ⟨_, rfl⟩
  have hsb : ∀ i : Fin n, s i b = (if i.val < j then 0 else if i.val = j then 2 else 4) := by
    intro i; simp [hs]
  have hsa : ∀ i : Fin n,
      s i a = (if i.val = j then 1 else if (P i).rel a c then 1 else 3) := by
    intro i; simp [hs, hab]
  have hsc : ∀ i : Fin n,
      s i c = (if i.val = j then 3 else if (P i).rel a c then 3 else 1) := by
    intro i; simp [hs, hcb, Ne.symm hac]
  -- `R` and `Pi j` agree on the pair `(a, b)`.
  have hmab : ∀ i : Fin n, ((R i).rel a b ↔ (Pi j i).rel a b) := by
    intro i
    rcases lt_trichotomy i.val j with h | h | h
    · refine iff_of_false ?_ ?_
      · simp only [hR]
        exact scoreRanking_not_rel (by rw [hsa i, hsb i]; split_ifs <;> omega)
      · simp only [hPi]
        exact scoreRanking_not_rel (by rw [htb j i, htx j i a hab]; split_ifs <;> omega)
    · refine iff_of_true ?_ ?_
      · simp only [hR]
        exact scoreRanking_rel (by rw [hsa i, hsb i]; split_ifs <;> omega)
      · simp only [hPi]
        exact scoreRanking_rel (by rw [htb j i, htx j i a hab]; split_ifs <;> omega)
    · refine iff_of_true ?_ ?_
      · simp only [hR]
        exact scoreRanking_rel (by rw [hsa i, hsb i]; split_ifs <;> omega)
      · simp only [hPi]
        exact scoreRanking_rel (by rw [htb j i, htx j i a hab]; split_ifs <;> omega)
  -- `R` and `Pi (j+1)` agree on the pair `(b, c)`.
  have hmbc : ∀ i : Fin n, ((R i).rel b c ↔ (Pi (j + 1) i).rel b c) := by
    intro i
    rcases lt_trichotomy i.val j with h | h | h
    · refine iff_of_true ?_ ?_
      · simp only [hR]
        exact scoreRanking_rel (by rw [hsc i, hsb i]; split_ifs <;> omega)
      · simp only [hPi]
        exact scoreRanking_rel (by rw [htb (j + 1) i, htx (j + 1) i c hcb]; split_ifs <;> omega)
    · refine iff_of_true ?_ ?_
      · simp only [hR]
        exact scoreRanking_rel (by rw [hsc i, hsb i]; split_ifs <;> omega)
      · simp only [hPi]
        exact scoreRanking_rel (by rw [htb (j + 1) i, htx (j + 1) i c hcb]; split_ifs <;> omega)
    · refine iff_of_false ?_ ?_
      · simp only [hR]
        exact scoreRanking_not_rel (by rw [hsc i, hsb i]; split_ifs <;> omega)
      · simp only [hPi]
        exact scoreRanking_not_rel
          (by rw [htb (j + 1) i, htx (j + 1) i c hcb]; split_ifs <;> omega)
  have hFRab : (F R).rel a b := (hI R (Pi j) a b hmab).mpr (hbotj a hab)
  have hFRbc : (F R).rel b c := (hI R (Pi (j + 1)) b c hmbc).mpr (htopk c hcb)
  have hFRac : (F R).rel a c := (F R).rel_trans hFRab hFRbc
  -- `R` and `P` agree on the pair `(a, c)`.
  have hmac : ∀ i : Fin n, ((R i).rel a c ↔ (P i).rel a c) := by
    intro i
    by_cases h : i.val = j
    · have hi : i = ⟨j, hjn⟩ := Fin.ext h
      subst hi
      refine iff_of_true ?_ hP
      simp only [hR]
      exact scoreRanking_rel (by rw [hsa, hsc]; split_ifs; omega)
    · by_cases hp : (P i).rel a c
      · refine iff_of_true ?_ hp
        simp only [hR]
        exact scoreRanking_rel (by rw [hsa i, hsc i]; split_ifs; omega)
      · refine iff_of_false ?_ hp
        simp only [hR]
        exact scoreRanking_not_rel (by rw [hsa i, hsc i]; split_ifs; omega)
  exact (hI P R a c (fun i => (hmac i).symm)).mpr hFRac

/-! ## Arrow's theorem -/

/-- **Arrow's theorem**, dictatorship form: a social welfare function on at least three
alternatives, for a finite nonempty electorate, that satisfies unanimity and independence of
irrelevant alternatives has a dictator. -/
theorem exists_dictator {A V : Type*} [Fintype V] [Nonempty V] {F : SWF V A}
    (hU : Unanimity F) (hI : IIA F)
    (hA : ∃ e₁ e₂ e₃ : A, e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃) :
    ∃ v : V, Dictator F v := by
  classical
  obtain ⟨e₁, e₂, e₃, h12, h13, h23⟩ := hA
  obtain ⟨eq⟩ : Nonempty (V ≃ Fin (Fintype.card V)) := ⟨Fintype.equivFin V⟩
  obtain ⟨G, hG⟩ : ∃ G : SWF (Fin (Fintype.card V)) A, G = fun Q => F (fun v => Q (eq v)) :=
    ⟨_, rfl⟩
  have hUG : Unanimity G := by
    intro Q x y h; simp only [hG]; exact hU _ x y (fun v => h (eq v))
  have hIG : IIA G := by
    intro Q₁ Q₂ x y h; simp only [hG]; exact hI _ _ x y (fun v => h (eq v))
  obtain ⟨i, hi⟩ := exists_decisive_fin hUG hIG h12 (Ne.symm h23) h13
  refine ⟨eq.symm i, ?_⟩
  have hdec : Decisive F (eq.symm i) e₁ e₃ := by
    intro P hP
    have h0 : (fun v => P (eq.symm (eq v))) = P := by
      funext v; rw [Equiv.symm_apply_apply]
    have h1 := hi (fun k => P (eq.symm k)) hP
    simp only [hG, h0] at h1
    exact h1
  exact dictator_of_decisive hU hI h13 hdec h12 h13 h23

/-- **Arrow's impossibility theorem.**  For at least three alternatives and a finite nonempty
electorate, no social welfare function (i.e. no ranked voting rule producing a social ranking
from the voters' rankings) satisfies unanimity, independence of irrelevant alternatives and
non-dictatorship simultaneously. -/
theorem arrow_impossibility {A V : Type*} [Fintype V] [Nonempty V] (F : SWF V A)
    (hA : ∃ e₁ e₂ e₃ : A, e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃) :
    ¬ (Unanimity F ∧ IIA F ∧ ∀ v : V, ¬ Dictator F v) := by
  rintro ⟨hU, hI, hnd⟩
  obtain ⟨v, hv⟩ := exists_dictator hU hI hA
  exact hnd v hv

/-! ## Sanity checks: the conditions are not vacuous -/

/-- Dropping non-dictatorship, the remaining conditions are satisfiable: the rule "always copy
voter `v₀`'s ranking" is unanimous, satisfies IIA, and (of course) has `v₀` as a dictator. -/
theorem dictatorship_satisfies (v₀ : V) :
    Unanimity (fun P : V → Ranking A => P v₀) ∧ IIA (fun P : V → Ranking A => P v₀) ∧
      Dictator (fun P : V → Ranking A => P v₀) v₀ :=
  ⟨fun _ _ _ h => h v₀, fun _ _ _ _ h => h v₀, fun _ _ _ h => h⟩

/-- Dropping unanimity, the remaining conditions are satisfiable when there are at least two
alternatives: the constant rule (always output a fixed ranking `R₀`) satisfies IIA and has no
dictator. -/
theorem constant_rule_satisfies (R₀ : Ranking A) {p q : A} (hpq : p ≠ q) :
    IIA (fun _ : V → Ranking A => R₀) ∧ ∀ v : V, ¬ Dictator (fun _ : V → Ranking A => R₀) v := by
  refine ⟨fun _ _ _ _ _ => Iff.rfl, fun v hv => ?_⟩
  classical
  -- feed the rule a profile where `v` disagrees with `R₀`
  rcases R₀.rel_total p q hpq with h | h
  · obtain ⟨s, hs⟩ : ∃ s : A → ℕ, s = fun x => if x = q then 0 else 1 := ⟨_, rfl⟩
    have h1 : (scoreRanking s).rel q p := scoreRanking_rel (by simp [hs, hpq])
    exact R₀.asymm h (hv (fun _ => scoreRanking s) q p h1)
  · obtain ⟨s, hs⟩ : ∃ s : A → ℕ, s = fun x => if x = p then 0 else 1 := ⟨_, rfl⟩
    have h1 : (scoreRanking s).rel p q := scoreRanking_rel (by simp [hs, Ne.symm hpq])
    exact R₀.asymm h (hv (fun _ => scoreRanking s) p q h1)

/-- The base case: three alternatives and two voters.  No ranked voting rule for the three
alternatives `Fin 3` and the two voters `Fin 2` is unanimous, independent of irrelevant
alternatives and non-dictatorial. -/
theorem arrow_impossibility_three_two (F : SWF (Fin 2) (Fin 3)) :
    ¬ (Unanimity F ∧ IIA F ∧ ∀ v : Fin 2, ¬ Dictator F v) :=
  arrow_impossibility F ⟨0, 1, 2, by decide, by decide, by decide⟩

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

