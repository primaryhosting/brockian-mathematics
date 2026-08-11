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

import Mathlib

/-!
# Arrow's impossibility theorem

A *ranking* on a type of alternatives `A` is a total, transitive, antisymmetric relation
(a linear order presented as a relation).  A *profile* assigns a ranking to each voter, and a
*ranked voting rule* (social welfare function) aggregates profiles into a single relation.

The main result, `Frontier.arrow_impossibility`, states that whenever there are at least three
alternatives and finitely many voters, no ranked voting rule producing a ranking can
simultaneously satisfy unanimity (Pareto), independence of irrelevant alternatives, and
non-dictatorship.
-/

namespace Frontier

section Defs

variable {A : Type*}

/-- A *ranking* of the alternatives: a total, transitive, antisymmetric relation. -/
def IsRanking (r : A → A → Prop) : Prop :=
  (∀ a b, r a b ∨ r b a) ∧ (∀ a b c, r a b → r b c → r a c) ∧ (∀ a b, r a b → r b a → a = b)

/-- Strict preference associated to a ranking: `a` is weakly preferred to `b`, but not
conversely. -/
def SPref (r : A → A → Prop) (a b : A) : Prop := r a b ∧ ¬ r b a

/-- A profile assigns a preference relation to every voter. -/
abbrev Profile (V A : Type*) := V → A → A → Prop

variable {V : Type*}

/-- A profile is admissible when every voter's preference is a ranking. -/
def IsProfile (p : Profile V A) : Prop := ∀ v, IsRanking (p v)

/-- A ranked voting rule (social welfare function). -/
abbrev Rule (V A : Type*) := Profile V A → A → A → Prop

/-- The rule outputs a ranking on every admissible profile. -/
def IsRankingRule (F : Rule V A) : Prop := ∀ p, IsProfile p → IsRanking (F p)

/-- Unanimity (Pareto): if every voter strictly prefers `a` to `b`, so does society. -/
def Unanimity (F : Rule V A) : Prop :=
  ∀ p, IsProfile p → ∀ a b, (∀ v, SPref (p v) a b) → SPref (F p) a b

/-- Independence of irrelevant alternatives: the social ranking of the pair `a, b` depends
only on the individual rankings of the pair `a, b`. -/
def IIA (F : Rule V A) : Prop :=
  ∀ p q, IsProfile p → IsProfile q → ∀ a b,
    (∀ v, (p v a b ↔ q v a b)) → (∀ v, (p v b a ↔ q v b a)) → (F p a b ↔ F q a b)

/-- Voter `d` is decisive over the ordered pair `(a, b)`: whenever `d` strictly prefers `a`
to `b`, so does society. -/
def Decisive (F : Rule V A) (d : V) (a b : A) : Prop :=
  ∀ p, IsProfile p → SPref (p d) a b → SPref (F p) a b

/-- Voter `d` is decisive over every pair of alternatives avoiding `z`. -/
def LocalDict (F : Rule V A) (d : V) (z : A) : Prop :=
  ∀ x y : A, x ≠ z → y ≠ z → x ≠ y → Decisive F d x y

/-- Voter `d` is a dictator: society always follows `d`'s strict preferences. -/
def IsDictator (F : Rule V A) (d : V) : Prop :=
  ∀ p, IsProfile p → ∀ a b, SPref (p d) a b → SPref (F p) a b

end Defs

section Basic

variable {A : Type*} {r : A → A → Prop}

lemma IsRanking.total (h : IsRanking r) (a b : A) : r a b ∨ r b a := h.1 a b

lemma IsRanking.trans (h : IsRanking r) {a b c : A} (hab : r a b) (hbc : r b c) : r a c :=
  h.2.1 a b c hab hbc

lemma IsRanking.antisymm (h : IsRanking r) {a b : A} (hab : r a b) (hba : r b a) : a = b :=
  h.2.2 a b hab hba

lemma IsRanking.refl (h : IsRanking r) (a : A) : r a a := (h.total a a).elim id id

lemma spref_iff (h : IsRanking r) (a b : A) : SPref r a b ↔ ¬ r b a := by
  constructor
  · rintro ⟨_, h2⟩; exact h2
  · intro hba
    exact ⟨(h.total a b).resolve_right hba, hba⟩

lemma spref_trans (h : IsRanking r) {a b c : A} (h1 : SPref r a b) (h2 : SPref r b c) :
    SPref r a c :=
  ⟨h.trans h1.1 h2.1, fun hca => h2.2 (h.trans hca h1.1)⟩

lemma spref_ne {a b : A} (h1 : SPref r a b) : a ≠ b := by
  rintro rfl; exact h1.2 h1.1

/-- Two relations agreeing on a strictly preferred pair agree on both orderings of the pair. -/
lemma spref_pair_iff {r₁ r₂ : A → A → Prop} {s t : A} (h₁ : SPref r₁ s t) (h₂ : SPref r₂ s t) :
    (r₁ s t ↔ r₂ s t) ∧ (r₁ t s ↔ r₂ t s) :=
  ⟨iff_of_true h₁.1 h₂.1, iff_of_false h₁.2 h₂.2⟩

/-- Variant of `spref_pair_iff` with the strict preference in the other direction. -/
lemma spref_pair_iff' {r₁ r₂ : A → A → Prop} {s t : A} (h₁ : SPref r₁ t s) (h₂ : SPref r₂ t s) :
    (r₁ s t ↔ r₂ s t) ∧ (r₁ t s ↔ r₂ t s) :=
  ⟨iff_of_false h₁.2 h₂.2, iff_of_true h₁.1 h₂.1⟩

end Basic

section Ops

variable {A : Type*}

/-- Modify a relation by moving `b` to the top. -/
def putTop (b : A) (r : A → A → Prop) : A → A → Prop := fun s t => s = b ∨ (t ≠ b ∧ r s t)

/-- Modify a relation by moving `b` to the bottom. -/
def putBot (b : A) (r : A → A → Prop) : A → A → Prop := fun s t => t = b ∨ (s ≠ b ∧ r s t)

/-- Modify a relation by moving `z` to the position immediately above `w`. -/
def liftAbove (z w : A) (r : A → A → Prop) : A → A → Prop := fun s t =>
  (s = z ∧ t = z) ∨ (s = z ∧ t ≠ z ∧ r w t) ∨ (s ≠ z ∧ t = z ∧ r s w ∧ s ≠ w) ∨
    (s ≠ z ∧ t ≠ z ∧ r s t)

variable {r : A → A → Prop} {b z w : A}

lemma isRanking_putTop (h : IsRanking r) (b : A) : IsRanking (putTop b r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s t
    by_cases hs : s = b
    · exact Or.inl (Or.inl hs)
    · by_cases ht : t = b
      · exact Or.inr (Or.inl ht)
      · rcases h.total s t with hst | hts
        · exact Or.inl (Or.inr ⟨ht, hst⟩)
        · exact Or.inr (Or.inr ⟨hs, hts⟩)
  · rintro s t u (rfl | ⟨ht, hst⟩) htu
    · exact Or.inl rfl
    · rcases htu with (rfl | ⟨hu, htu⟩)
      · exact absurd rfl ht
      · exact Or.inr ⟨hu, h.trans hst htu⟩
  · rintro s t (rfl | ⟨ht, hst⟩) hts
    · rcases hts with (rfl | ⟨h1, _⟩)
      · rfl
      · exact absurd rfl h1
    · rcases hts with (rfl | ⟨_, hts⟩)
      · exact absurd rfl ht
      · exact h.antisymm hst hts

lemma isRanking_putBot (h : IsRanking r) (b : A) : IsRanking (putBot b r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s t
    by_cases ht : t = b
    · exact Or.inl (Or.inl ht)
    · by_cases hs : s = b
      · exact Or.inr (Or.inl hs)
      · rcases h.total s t with hst | hts
        · exact Or.inl (Or.inr ⟨hs, hst⟩)
        · exact Or.inr (Or.inr ⟨ht, hts⟩)
  · rintro s t u hst (rfl | ⟨ht, htu⟩)
    · exact Or.inl rfl
    · rcases hst with (rfl | ⟨hs, hst⟩)
      · exact absurd rfl ht
      · exact Or.inr ⟨hs, h.trans hst htu⟩
  · rintro s t (rfl | ⟨hs, hst⟩) hts
    · rcases hts with (rfl | ⟨h1, _⟩)
      · rfl
      · exact absurd rfl h1
    · rcases hts with (rfl | ⟨_, hts⟩)
      · exact absurd rfl hs
      · exact h.antisymm hst hts

lemma putTop_of_ne {s t : A} (hs : s ≠ b) (ht : t ≠ b) : putTop b r s t ↔ r s t := by
  simp [putTop, hs, ht]

lemma putBot_of_ne {s t : A} (hs : s ≠ b) (ht : t ≠ b) : putBot b r s t ↔ r s t := by
  simp [putBot, hs, ht]

lemma spref_putTop {x : A} (hx : x ≠ b) : SPref (putTop b r) b x := by
  refine ⟨Or.inl rfl, ?_⟩
  simp [putTop, hx]

lemma spref_putBot {x : A} (hx : x ≠ b) : SPref (putBot b r) x b := by
  refine ⟨Or.inl rfl, ?_⟩
  simp [putBot, hx]

lemma spref_putTop_of_ne {x y : A} (hx : x ≠ b) (hy : y ≠ b) (h : SPref r x y) :
    SPref (putTop b r) x y :=
  ⟨(putTop_of_ne hx hy).2 h.1, fun hc => h.2 ((putTop_of_ne hy hx).1 hc)⟩

lemma liftAbove_self : liftAbove z w r z z := Or.inl ⟨rfl, rfl⟩

lemma liftAbove_left {t : A} (ht : t ≠ z) : liftAbove z w r z t ↔ r w t := by
  simp [liftAbove, ht]

lemma liftAbove_right {s : A} (hs : s ≠ z) : liftAbove z w r s z ↔ (r s w ∧ s ≠ w) := by
  simp [liftAbove, hs]

lemma liftAbove_of_ne {s t : A} (hs : s ≠ z) (ht : t ≠ z) :
    liftAbove z w r s t ↔ r s t := by
  simp [liftAbove, hs, ht]

lemma isRanking_liftAbove (h : IsRanking r) : IsRanking (liftAbove z w r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s t
    by_cases hs : s = z <;> by_cases ht : t = z
    · subst hs; subst ht; exact Or.inl liftAbove_self
    · subst hs
      by_cases htw : t = w
      · subst htw; exact Or.inl ((liftAbove_left ht).2 (h.refl t))
      · rcases h.total w t with h1 | h1
        · exact Or.inl ((liftAbove_left ht).2 h1)
        · exact Or.inr ((liftAbove_right ht).2 ⟨h1, htw⟩)
    · subst ht
      by_cases hsw : s = w
      · subst hsw; exact Or.inr ((liftAbove_left hs).2 (h.refl s))
      · rcases h.total s w with h1 | h1
        · exact Or.inl ((liftAbove_right hs).2 ⟨h1, hsw⟩)
        · exact Or.inr ((liftAbove_left hs).2 h1)
    · rcases h.total s t with h1 | h1
      · exact Or.inl ((liftAbove_of_ne hs ht).2 h1)
      · exact Or.inr ((liftAbove_of_ne ht hs).2 h1)
  · intro s t u hst htu
    by_cases hs : s = z <;> by_cases ht : t = z <;> by_cases hu : u = z
    · subst hs; subst hu; exact liftAbove_self
    · subst hs; subst ht; exact htu
    · subst hs; subst hu; exact liftAbove_self
    · subst hs
      rw [liftAbove_left ht] at hst
      rw [liftAbove_of_ne ht hu] at htu
      exact (liftAbove_left hu).2 (h.trans hst htu)
    · subst ht; subst hu; exact hst
    · subst ht
      rw [liftAbove_right hs] at hst
      rw [liftAbove_left hu] at htu
      exact (liftAbove_of_ne hs hu).2 (h.trans hst.1 htu)
    · subst hu
      rw [liftAbove_of_ne hs ht] at hst
      rw [liftAbove_right ht] at htu
      refine (liftAbove_right hs).2 ⟨h.trans hst htu.1, ?_⟩
      rintro rfl
      exact htu.2 (h.antisymm htu.1 hst)
    · rw [liftAbove_of_ne hs ht] at hst
      rw [liftAbove_of_ne ht hu] at htu
      exact (liftAbove_of_ne hs hu).2 (h.trans hst htu)
  · intro s t hst hts
    by_cases hs : s = z <;> by_cases ht : t = z
    · rw [hs, ht]
    · subst hs
      rw [liftAbove_left ht] at hst
      rw [liftAbove_right ht] at hts
      exact absurd (h.antisymm hts.1 hst) hts.2
    · subst ht
      rw [liftAbove_right hs] at hst
      rw [liftAbove_left hs] at hts
      exact absurd (h.antisymm hst.1 hts) hst.2
    · rw [liftAbove_of_ne hs ht] at hst
      rw [liftAbove_of_ne ht hs] at hts
      exact h.antisymm hst hts

lemma spref_liftAbove_self (h : IsRanking r) (hzw : z ≠ w) : SPref (liftAbove z w r) z w := by
  refine ⟨(liftAbove_left (Ne.symm hzw)).2 (h.refl w), ?_⟩
  rw [liftAbove_right (Ne.symm hzw)]
  rintro ⟨-, hc⟩
  exact hc rfl

lemma spref_liftAbove_of_spref {s : A} (hs : s ≠ z) (hsw : SPref r s w) :
    SPref (liftAbove z w r) s z := by
  refine ⟨(liftAbove_right hs).2 ⟨hsw.1, spref_ne hsw⟩, ?_⟩
  rw [liftAbove_left hs]
  exact hsw.2

/-- If `b` is at the top of `r` then it is still at the top after lifting `z` above `w`. -/
lemma spref_liftAbove_top (hbz : b ≠ z) (hbw : b ≠ w) (hb : ∀ x, x ≠ b → SPref r b x) :
    ∀ x, x ≠ b → SPref (liftAbove z w r) b x := by
  intro x hx
  by_cases hxz : x = z
  · subst hxz
    refine ⟨(liftAbove_right hbz).2 ⟨(hb w (Ne.symm hbw)).1, hbw⟩, ?_⟩
    rw [liftAbove_left hbz]
    exact (hb w (Ne.symm hbw)).2
  · exact ⟨(liftAbove_of_ne hbz hxz).2 (hb x hx).1,
      fun hc => (hb x hx).2 ((liftAbove_of_ne hxz hbz).1 hc)⟩

/-- If `b` is at the bottom of `r` then it is still at the bottom after lifting `z` above `w`. -/
lemma spref_liftAbove_bot (hbz : b ≠ z) (hbw : b ≠ w) (hb : ∀ x, x ≠ b → SPref r x b) :
    ∀ x, x ≠ b → SPref (liftAbove z w r) x b := by
  intro x hx
  by_cases hxz : x = z
  · subst hxz
    refine ⟨(liftAbove_left hbz).2 (hb w (Ne.symm hbw)).1, ?_⟩
    rw [liftAbove_right hbz]
    exact fun hc => (hb w (Ne.symm hbw)).2 hc.1
  · exact ⟨(liftAbove_of_ne hxz hbz).2 (hb x hx).1,
      fun hc => (hb x hx).2 ((liftAbove_of_ne hbz hxz).1 hc)⟩

end Ops

/-- Every type carries at least one ranking. -/
lemma exists_ranking (A : Type*) : ∃ r : A → A → Prop, IsRanking r := by
  letI : LinearOrder A := IsWellOrder.linearOrder (WellOrderingRel (α := A))
  exact ⟨(· ≤ ·), fun a b => le_total a b, fun _ _ _ => le_trans, fun _ _ => le_antisymm⟩

section Arrow

variable {V A : Type*} [Fintype V] {F : Rule V A}

omit [Fintype V] in
/-- Independence of irrelevant alternatives transfers strict social preferences. -/
lemma iia_spref (hI : IIA F) {p q : Profile V A} (hp : IsProfile p) (hq : IsProfile q) (a b : A)
    (h1 : ∀ v, (p v a b ↔ q v a b)) (h2 : ∀ v, (p v b a ↔ q v b a)) (hab : SPref (F p) a b) :
    SPref (F q) a b :=
  ⟨(hI p q hp hq a b h1 h2).1 hab.1, fun hc => hab.2 ((hI p q hp hq b a h2 h1).2 hc)⟩

omit [Fintype V] in
/-- **Extremal lemma**: if every voter puts `b` at the very top or the very bottom of their
ranking, then society puts `b` at the very top or the very bottom. -/
lemma extremal (hR : IsRankingRule F) (hU : Unanimity F) (hI : IIA F)
    (b : A) (p : Profile V A) (hp : IsProfile p)
    (hext : ∀ v, (∀ x, x ≠ b → SPref (p v) b x) ∨ (∀ x, x ≠ b → SPref (p v) x b)) :
    (∀ x, x ≠ b → SPref (F p) b x) ∨ (∀ x, x ≠ b → SPref (F p) x b) := by
  have hFp : IsRanking (F p) := hR p hp
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnotTop, hnotBot⟩ := hcon
  obtain ⟨a₁, ha₁, ha₁'⟩ := hnotTop
  obtain ⟨a₂, ha₂, ha₂'⟩ := hnotBot
  rw [spref_iff hFp] at ha₁' ha₂'
  push_neg at ha₁' ha₂'
  -- `ha₁' : F p a₁ b` and `ha₂' : F p b a₂`
  have hne : a₁ ≠ a₂ := by
    rintro rfl
    exact ha₁ (hFp.antisymm ha₁' ha₂')
  set q : Profile V A := fun v => liftAbove a₂ a₁ (p v) with hq_def
  have hq : IsProfile q := fun v => isRanking_liftAbove (hp v)
  -- everybody strictly prefers `a₂` to `a₁` in `q`
  have huna : SPref (F q) a₂ a₁ :=
    hU q hq a₂ a₁ fun v => spref_liftAbove_self (hp v) (Ne.symm hne)
  -- the pair `(a₁, b)` is untouched
  have hpair₁ : F p a₁ b ↔ F q a₁ b :=
    hI p q hp hq a₁ b
      (fun _ => (liftAbove_of_ne hne (Ne.symm ha₂)).symm)
      (fun _ => (liftAbove_of_ne (Ne.symm ha₂) hne).symm)
  -- the pair `(b, a₂)` is untouched, since `b` stays extremal
  have hpair₂ : ∀ v, (p v b a₂ ↔ q v b a₂) ∧ (p v a₂ b ↔ q v a₂ b) := by
    intro v
    rcases hext v with h | h
    · have h1 := h a₂ ha₂
      have h2 := spref_liftAbove_top (r := p v) (z := a₂) (w := a₁)
        (Ne.symm ha₂) (Ne.symm ha₁) h a₂ ha₂
      exact ⟨by simp only [hq_def]; exact iff_of_true h1.1 h2.1,
        by simp only [hq_def]; exact iff_of_false h1.2 h2.2⟩
    · have h1 := h a₂ ha₂
      have h2 := spref_liftAbove_bot (r := p v) (z := a₂) (w := a₁)
        (Ne.symm ha₂) (Ne.symm ha₁) h a₂ ha₂
      exact ⟨by simp only [hq_def]; exact iff_of_false h1.2 h2.2,
        by simp only [hq_def]; exact iff_of_true h1.1 h2.1⟩
  have hpair₂' : F p b a₂ ↔ F q b a₂ :=
    hI p q hp hq b a₂ (fun v => (hpair₂ v).1) (fun v => (hpair₂ v).2)
  have hFq : IsRanking (F q) := hR q hq
  exact huna.2 (hFq.trans (hpair₁.1 ha₁') (hpair₂'.1 ha₂'))

/-- Existence of a pivotal set for a predicate on finite sets. -/
lemma exists_pivotal {W : Type*} [DecidableEq W] (P : Finset W → Prop)
    (h0 : ¬ P ∅) (S : Finset W) (hS : P S) :
    ∃ (T : Finset W) (v : W), v ∉ T ∧ ¬ P T ∧ P (insert v T) := by
  induction S using Finset.induction with
  | empty => exact absurd hS h0
  | insert v S hv ih =>
    by_cases h : P S
    · exact ih h
    · exact ⟨S, v, hv, h, hS⟩

/-- **Pivotal voter lemma**: for each alternative `b` there is a voter who is decisive over
every pair of alternatives distinct from `b`. -/
lemma exists_localDict (hR : IsRankingRule F) (hU : Unanimity F) (hI : IIA F)
    (b : A) (hb : ∃ x : A, x ≠ b) :
    ∃ d : V, LocalDict F d b := by
  classical
  obtain ⟨x₀, hx₀⟩ := hb
  obtain ⟨r₀, hr₀⟩ := exists_ranking A
  -- `Q S` is the profile in which the voters of `S` put `b` on top and the others at the bottom
  set Q : Finset V → Profile V A := fun S v => if v ∈ S then putTop b r₀ else putBot b r₀
    with hQ_def
  have hQmem : ∀ (S : Finset V) (v : V), v ∈ S → Q S v = putTop b r₀ := by
    intro S v hv; simp only [hQ_def, if_pos hv]
  have hQnot : ∀ (S : Finset V) (v : V), v ∉ S → Q S v = putBot b r₀ := by
    intro S v hv; simp only [hQ_def, if_neg hv]
  have hQprof : ∀ S, IsProfile (Q S) := by
    intro S v
    by_cases hv : v ∈ S
    · rw [hQmem S v hv]; exact isRanking_putTop hr₀ b
    · rw [hQnot S v hv]; exact isRanking_putBot hr₀ b
  -- `P S` says that society puts `b` on top for the profile `Q S`
  set P : Finset V → Prop := fun S => ∀ x, x ≠ b → SPref (F (Q S)) b x with hP_def
  have hP0 : ¬ P ∅ := by
    intro hcon
    have h1 : SPref (F (Q ∅)) x₀ b := by
      refine hU _ (hQprof _) x₀ b fun v => ?_
      rw [hQnot ∅ v (Finset.notMem_empty v)]
      exact spref_putBot hx₀
    exact h1.2 (hcon x₀ hx₀).1
  have hPuniv : P Finset.univ := by
    intro x hx
    refine hU _ (hQprof _) b x fun v => ?_
    rw [hQmem Finset.univ v (Finset.mem_univ v)]
    exact spref_putTop hx
  obtain ⟨T, d, hdT, hnT, hT⟩ := exists_pivotal P hP0 Finset.univ hPuniv
  -- at the pivotal set `T`, society puts `b` at the bottom
  have hbotT : ∀ x, x ≠ b → SPref (F (Q T)) x b := by
    refine (extremal hR hU hI b (Q T) (hQprof T) fun v => ?_).resolve_left hnT
    by_cases hv : v ∈ T
    · exact Or.inl fun x hx => by rw [hQmem T v hv]; exact spref_putTop hx
    · exact Or.inr fun x hx => by rw [hQnot T v hv]; exact spref_putBot hx
  refine ⟨d, ?_⟩
  intro x y hxb hyb hxy p hp hs
  -- the auxiliary profile `q`: the pivotal voter inserts `b` just above `y`,
  -- the voters of `T` put `b` on top, and all the others put `b` at the bottom
  set q : Profile V A := fun v =>
    if v = d then liftAbove b y (p v)
    else if v ∈ T then putTop b (p v) else putBot b (p v) with hq_def
  have hqd : q d = liftAbove b y (p d) := by simp only [hq_def, if_pos rfl]
  have hqT : ∀ v, v ≠ d → v ∈ T → q v = putTop b (p v) := by
    intro v h1 h2; simp only [hq_def, if_neg h1, if_pos h2]
  have hqN : ∀ v, v ≠ d → v ∉ T → q v = putBot b (p v) := by
    intro v h1 h2; simp only [hq_def, if_neg h1, if_neg h2]
  have hqprof : IsProfile q := by
    intro v
    by_cases hv : v = d
    · subst hv; rw [hqd]; exact isRanking_liftAbove (hp v)
    · by_cases hvT : v ∈ T
      · rw [hqT v hv hvT]; exact isRanking_putTop (hp v) b
      · rw [hqN v hv hvT]; exact isRanking_putBot (hp v) b
  -- society ranks `x` above `b`
  have hpair₁ : ∀ v, (Q T v x b ↔ q v x b) ∧ (Q T v b x ↔ q v b x) := by
    intro v
    by_cases hv : v = d
    · subst hv
      refine spref_pair_iff ?_ ?_
      · rw [hQnot T v hdT]; exact spref_putBot hxb
      · rw [hqd]; exact spref_liftAbove_of_spref hxb hs
    · by_cases hvT : v ∈ T
      · refine spref_pair_iff' ?_ ?_
        · rw [hQmem T v hvT]; exact spref_putTop hxb
        · rw [hqT v hv hvT]; exact spref_putTop hxb
      · refine spref_pair_iff ?_ ?_
        · rw [hQnot T v hvT]; exact spref_putBot hxb
        · rw [hqN v hv hvT]; exact spref_putBot hxb
  have hxb' : SPref (F q) x b :=
    iia_spref hI (hQprof T) hqprof x b (fun v => (hpair₁ v).1) (fun v => (hpair₁ v).2)
      (hbotT x hxb)
  -- society ranks `b` above `y`
  have hpair₂ : ∀ v, (Q (insert d T) v b y ↔ q v b y) ∧ (Q (insert d T) v y b ↔ q v y b) := by
    intro v
    by_cases hv : v = d
    · subst hv
      refine spref_pair_iff ?_ ?_
      · rw [hQmem _ v (Finset.mem_insert_self v T)]; exact spref_putTop hyb
      · rw [hqd]; exact spref_liftAbove_self (hp v) (Ne.symm hyb)
    · by_cases hvT : v ∈ T
      · refine spref_pair_iff ?_ ?_
        · rw [hQmem _ v (Finset.mem_insert_of_mem hvT)]; exact spref_putTop hyb
        · rw [hqT v hv hvT]; exact spref_putTop hyb
      · have hvI : v ∉ insert d T := by
          simp only [Finset.mem_insert]
          push_neg
          exact ⟨hv, hvT⟩
        refine spref_pair_iff' ?_ ?_
        · rw [hQnot _ v hvI]; exact spref_putBot hyb
        · rw [hqN v hv hvT]; exact spref_putBot hyb
  have hby' : SPref (F q) b y :=
    iia_spref hI (hQprof _) hqprof b y (fun v => (hpair₂ v).1) (fun v => (hpair₂ v).2)
      (hT y hyb)
  have hxy' : SPref (F q) x y := spref_trans (hR q hqprof) hxb' hby'
  -- transfer back to the original profile: the pair `x, y` was never touched
  have hpair₃ : ∀ v, (q v x y ↔ p v x y) ∧ (q v y x ↔ p v y x) := by
    intro v
    by_cases hv : v = d
    · subst hv
      rw [hqd]
      exact ⟨liftAbove_of_ne hxb hyb, liftAbove_of_ne hyb hxb⟩
    · by_cases hvT : v ∈ T
      · rw [hqT v hv hvT]
        exact ⟨putTop_of_ne hxb hyb, putTop_of_ne hyb hxb⟩
      · rw [hqN v hv hvT]
        exact ⟨putBot_of_ne hxb hyb, putBot_of_ne hyb hxb⟩
  exact iia_spref hI hqprof hp x y (fun v => (hpair₃ v).1) (fun v => (hpair₃ v).2) hxy'

omit [Fintype V] in
/-- Two voters decisive over overlapping pairs of distinct alternatives coincide. -/
lemma decisive_unique (hR : IsRankingRule F) (hU : Unanimity F)
    {d₁ d₂ : V} {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1 : Decisive F d₁ x y) (h2 : Decisive F d₂ y z) : d₁ = d₂ := by
  by_contra hne
  classical
  obtain ⟨r₀, hr₀⟩ := exists_ranking A
  -- `R₁` ranks `z > x > y`, `R₂` ranks `y > z > x`
  set R₁ : A → A → Prop := putTop z (putTop x (putTop y r₀)) with hR₁
  set R₂ : A → A → Prop := putTop y (putTop z (putTop x r₀)) with hR₂
  have hR₁rank : IsRanking R₁ :=
    isRanking_putTop (isRanking_putTop (isRanking_putTop hr₀ y) x) z
  have hR₂rank : IsRanking R₂ :=
    isRanking_putTop (isRanking_putTop (isRanking_putTop hr₀ x) z) y
  have hR₁zx : SPref R₁ z x := spref_putTop hxz
  have hR₁xy : SPref R₁ x y := spref_putTop_of_ne hxz hyz (spref_putTop (Ne.symm hxy))
  have hR₂yz : SPref R₂ y z := spref_putTop (Ne.symm hyz)
  have hR₂zx : SPref R₂ z x := spref_putTop_of_ne (Ne.symm hyz) hxy (spref_putTop hxz)
  set q : Profile V A := fun v => if v = d₂ then R₂ else R₁ with hq_def
  have hqval : ∀ v, (v = d₂ → q v = R₂) ∧ (v ≠ d₂ → q v = R₁) := by
    intro v
    exact ⟨fun hv => if_pos hv, fun hv => if_neg hv⟩
  have hq : IsProfile q := by
    intro v
    by_cases hv : v = d₂
    · rw [(hqval v).1 hv]; exact hR₂rank
    · rw [(hqval v).2 hv]; exact hR₁rank
  have hxy' : SPref (F q) x y := h1 q hq (by rw [(hqval d₁).2 hne]; exact hR₁xy)
  have hyz' : SPref (F q) y z := h2 q hq (by rw [(hqval d₂).1 rfl]; exact hR₂yz)
  have hzx' : SPref (F q) z x := by
    refine hU q hq z x fun v => ?_
    by_cases hv : v = d₂
    · rw [(hqval v).1 hv]; exact hR₂zx
    · rw [(hqval v).2 hv]; exact hR₁zx
  exact hzx'.2 (spref_trans (hR q hq) hxy' hyz').1

omit [Fintype V] in
/-- Local dictators for different alternatives coincide. -/
lemma localDict_eq_of_ne (hR : IsRankingRule F) (hU : Unanimity F)
    {d₁ d₂ : V} {z₁ z₂ : A} (hz : z₁ ≠ z₂) (ht : ∃ t : A, t ≠ z₁ ∧ t ≠ z₂)
    (h1 : LocalDict F d₁ z₁) (h2 : LocalDict F d₂ z₂) : d₁ = d₂ := by
  obtain ⟨t, ht₁, ht₂⟩ := ht
  exact decisive_unique hR hU (Ne.symm ht₂) (Ne.symm hz) ht₁
    (h1 z₂ t (Ne.symm hz) ht₁ (Ne.symm ht₂)) (h2 t z₁ ht₂ hz ht₁)

/-- With at least three alternatives, for every pair there is an alternative outside it. -/
lemma exists_ne_two (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) (x y : A) :
    ∃ t : A, t ≠ x ∧ t ≠ y := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := h3
  by_cases h1 : a ≠ x ∧ a ≠ y
  · exact ⟨a, h1⟩
  by_cases h2 : b ≠ x ∧ b ≠ y
  · exact ⟨b, h2⟩
  by_cases h3 : c ≠ x ∧ c ≠ y
  · exact ⟨c, h3⟩
  push_neg at h1 h2 h3
  have ha : a = x ∨ a = y := by by_cases h : a = x; exacts [Or.inl h, Or.inr (h1 h)]
  have hb : b = x ∨ b = y := by by_cases h : b = x; exacts [Or.inl h, Or.inr (h2 h)]
  have hc : c = x ∨ c = y := by by_cases h : c = x; exacts [Or.inl h, Or.inr (h3 h)]
  rcases ha with rfl | rfl <;> rcases hb with h | h <;> rcases hc with h' | h' <;> simp_all

/-- **Arrow's theorem** (existence-of-a-dictator form). -/
theorem exists_dictator (hR : IsRankingRule F) (hU : Unanimity F) (hI : IIA F)
    (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∃ d : V, IsDictator F d := by
  obtain ⟨a₀, b₀, c₀, hab, hac, hbc⟩ := h3
  have h3' : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c := ⟨a₀, b₀, c₀, hab, hac, hbc⟩
  obtain ⟨d, hd⟩ := exists_localDict hR hU hI a₀ ⟨b₀, Ne.symm hab⟩
  refine ⟨d, ?_⟩
  intro p hp x y hs
  have hxy : x ≠ y := spref_ne hs
  obtain ⟨z, hzx, hzy⟩ := exists_ne_two h3' x y
  by_cases hza : z = a₀
  · subst hza
    exact hd x y (Ne.symm hzx) (Ne.symm hzy) hxy p hp hs
  · obtain ⟨d', hd'⟩ := exists_localDict hR hU hI z ⟨a₀, fun h => hza h.symm⟩
    obtain ⟨t, ht₁, ht₂⟩ := exists_ne_two h3' z a₀
    have hdd : d' = d := localDict_eq_of_ne hR hU hza ⟨t, ht₁, ht₂⟩ hd' hd
    rw [hdd] at hd'
    exact hd' x y (Ne.symm hzx) (Ne.symm hzy) hxy p hp hs

end Arrow

/-- The three conditions are not vacuous: the dictatorial rule "society ranks as voter `d`
does" produces rankings and satisfies unanimity and independence of irrelevant alternatives
(it is, of course, dictatorial). -/
theorem dictatorial_rule_spec {V A : Type*} (d : V) :
    IsRankingRule (fun p : Profile V A => p d) ∧ Unanimity (fun p : Profile V A => p d) ∧
      IIA (fun p : Profile V A => p d) ∧ IsDictator (fun p : Profile V A => p d) d :=
  ⟨fun _ hp => hp d, fun _ _ _ _ h => h d, fun _ _ _ _ _ _ h1 _ => h1 d, fun _ _ _ _ h => h⟩

/-- **Arrow's impossibility theorem**: with at least three alternatives and finitely many
voters, no ranked voting rule satisfies unanimity, independence of irrelevant alternatives,
and non-dictatorship. -/
theorem arrow_impossibility {V A : Type*} [Fintype V]
    (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) (F : Rule V A) :
    ¬ (IsRankingRule F ∧ Unanimity F ∧ IIA F ∧ ∀ d : V, ¬ IsDictator F d) := by
  rintro ⟨hR, hU, hI, hnd⟩
  obtain ⟨d, hd⟩ := exists_dictator hR hU hI h3
  exact hnd d hd

end Frontier

