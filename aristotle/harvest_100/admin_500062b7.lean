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

A ranked voting rule (social welfare function) turns a profile of individual rankings of the
alternatives into a social ranking.  Arrow's theorem says that as soon as there are at least
three alternatives, no such rule can be unanimous (Pareto), independent of irrelevant
alternatives, and non-dictatorial at the same time.

The key intermediate result is the *field expansion* / contagion lemma
`Frontier.decisive_of_almostDecisiveFor`: a coalition that gets its way on one ordered pair of
alternatives against unanimous opposition is decisive for *every* ordered pair.  A minimal
decisive coalition is then shown to be a singleton, i.e. a dictator.
-/

namespace Frontier

/-- A *ranking* of the alternatives `α`: a total, transitive, antisymmetric relation, i.e. a
linear order given as a relation.  `rel x y` reads "`x` is at least as good as `y`". -/
structure Ranking (α : Type*) where
  rel : α → α → Prop
  rel_total : ∀ x y, rel x y ∨ rel y x
  rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
  rel_antisymm : ∀ {x y}, rel x y → rel y x → x = y

namespace Ranking

variable {α : Type*}

/-- Strict preference: `x` is ranked strictly above `y`. -/
def pref (r : Ranking α) (x y : α) : Prop := r.rel x y ∧ x ≠ y

lemma rel_refl (r : Ranking α) (x : α) : r.rel x x := (r.rel_total x x).elim id id

lemma pref_iff_not_rel (r : Ranking α) {x y : α} : r.pref x y ↔ ¬ r.rel y x := by
  constructor
  · rintro ⟨hxy, hne⟩ hyx
    exact hne (r.rel_antisymm hxy hyx)
  · intro h
    refine ⟨(r.rel_total x y).resolve_right h, ?_⟩
    rintro rfl
    exact h (r.rel_refl x)

lemma pref_asymm (r : Ranking α) {x y : α} (h : r.pref x y) : ¬ r.pref y x := by
  rw [pref_iff_not_rel] at h ⊢
  intro h'
  exact h ((r.rel_total y x).resolve_right h')

lemma pref_trans (r : Ranking α) {x y z : α} (h₁ : r.pref x y) (h₂ : r.pref y z) :
    r.pref x z := by
  refine ⟨r.rel_trans h₁.1 h₂.1, ?_⟩
  rintro rfl
  exact h₂.2 (r.rel_antisymm h₂.1 h₁.1)

lemma pref_total (r : Ranking α) {x y : α} (h : x ≠ y) : r.pref x y ∨ r.pref y x := by
  rcases r.rel_total x y with h' | h'
  · exact Or.inl ⟨h', h⟩
  · exact Or.inr ⟨h', h.symm⟩

lemma not_pref_self (r : Ranking α) (x : α) : ¬ r.pref x x := fun h => h.2 rfl

/-- The reversed ranking. -/
def dual (r : Ranking α) : Ranking α where
  rel x y := r.rel y x
  rel_total x y := r.rel_total y x
  rel_trans h h' := r.rel_trans h' h
  rel_antisymm h h' := r.rel_antisymm h' h

lemma dual_pref (r : Ranking α) {x y : α} : (dual r).pref x y ↔ r.pref y x := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩

/-- Move the alternative `b` to the top of the ranking `r`, keeping everything else in place. -/
def moveTop (b : α) (r : Ranking α) : Ranking α where
  rel x y := x = b ∨ (y ≠ b ∧ r.rel x y)
  rel_total x y := by
    by_cases hx : x = b
    · exact Or.inl (Or.inl hx)
    · by_cases hy : y = b
      · exact Or.inr (Or.inl hy)
      · rcases r.rel_total x y with h | h
        · exact Or.inl (Or.inr ⟨hy, h⟩)
        · exact Or.inr (Or.inr ⟨hx, h⟩)
  rel_trans := by
    rintro x y z (rfl | ⟨hy, hxy⟩) hyz
    · exact Or.inl rfl
    · rcases hyz with rfl | ⟨hz, hyz⟩
      · exact absurd rfl hy
      · exact Or.inr ⟨hz, r.rel_trans hxy hyz⟩
  rel_antisymm := by
    rintro x y (rfl | ⟨hy, hxy⟩) hyx
    · rcases hyx with rfl | ⟨hy, _⟩
      · rfl
      · exact absurd rfl hy
    · rcases hyx with rfl | ⟨_, hyx⟩
      · exact absurd rfl hy
      · exact r.rel_antisymm hxy hyx

lemma moveTop_pref_top (b : α) (r : Ranking α) {x : α} (hx : x ≠ b) :
    (moveTop b r).pref b x := ⟨Or.inl rfl, fun h => hx h.symm⟩

lemma moveTop_pref (b : α) (r : Ranking α) {x y : α} (hx : x ≠ b) (hy : y ≠ b) :
    (moveTop b r).pref x y ↔ r.pref x y := by
  constructor
  · rintro ⟨h1 | ⟨-, h1⟩, h2⟩
    · exact absurd h1 hx
    · exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inr ⟨hy, h1⟩, h2⟩

/-- Move the alternative `b` to the bottom of the ranking `r`, keeping everything else in
place. -/
def moveBot (b : α) (r : Ranking α) : Ranking α := dual (moveTop b (dual r))

lemma moveBot_pref_bot (b : α) (r : Ranking α) {x : α} (hx : x ≠ b) :
    (moveBot b r).pref x b := by
  rw [moveBot, dual_pref]
  exact moveTop_pref_top b (dual r) hx

lemma moveBot_pref (b : α) (r : Ranking α) {x y : α} (hx : x ≠ b) (hy : y ≠ b) :
    (moveBot b r).pref x y ↔ r.pref x y := by
  rw [moveBot, dual_pref, moveTop_pref b (dual r) hy hx, dual_pref]

/-- The ranking `r` modified so that `x`, `y`, `z` occupy the top three positions, in this
order. -/
def top3 (x y z : α) (r : Ranking α) : Ranking α := moveTop x (moveTop y (moveTop z r))

lemma top3_pref_fst_snd {x y z : α} (r : Ranking α) (hxy : x ≠ y) :
    (top3 x y z r).pref x y := moveTop_pref_top x _ (Ne.symm hxy)

lemma top3_pref_fst_trd {x y z : α} (r : Ranking α) (hxz : x ≠ z) :
    (top3 x y z r).pref x z := moveTop_pref_top x _ (Ne.symm hxz)

lemma top3_pref_snd_trd {x y z : α} (r : Ranking α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (top3 x y z r).pref y z := by
  rw [top3, moveTop_pref x _ (Ne.symm hxy) (Ne.symm hxz)]
  exact moveTop_pref_top y _ (Ne.symm hyz)

/-- Every type carries at least one ranking. -/
instance instNonempty (α : Type*) : Nonempty (Ranking α) := by
  haveI := (@WellOrderingRel.isWellOrder α)
  haveI : DecidableRel (@WellOrderingRel α) := fun _ _ => Classical.propDecidable _
  letI : LinearOrder α := linearOrderOfSTO (@WellOrderingRel α)
  exact ⟨{ rel := fun x y => y ≤ x
           rel_total := fun x y => le_total y x
           rel_trans := fun h h' => le_trans h' h
           rel_antisymm := fun h h' => le_antisymm h' h }⟩

end Ranking

open Ranking

section Arrow

variable {V α : Type*} (F : (V → Ranking α) → Ranking α)

/-- Pareto/unanimity: if every voter strictly prefers `x` to `y`, so does society. -/
def Unanimous : Prop :=
  ∀ (p : V → Ranking α) (x y : α), (∀ i, (p i).pref x y) → (F p).pref x y

/-- Independence of irrelevant alternatives: the social ranking of `x` against `y` depends only
on the individual rankings of `x` against `y`. -/
def IIA : Prop :=
  ∀ (p q : V → Ranking α) (x y : α), (∀ i, ((p i).pref x y ↔ (q i).pref x y)) →
    ((F p).pref x y ↔ (F q).pref x y)

/-- Voter `i` is a dictator: society always follows `i`'s strict preferences. -/
def IsDictator (i : V) : Prop :=
  ∀ (p : V → Ranking α) (x y : α), (p i).pref x y → (F p).pref x y

/-- The coalition `G` is decisive for the ordered pair `(x, y)`. -/
def DecisiveFor (G : Finset V) (x y : α) : Prop :=
  ∀ p : V → Ranking α, (∀ i ∈ G, (p i).pref x y) → (F p).pref x y

/-- The coalition `G` is almost decisive for the ordered pair `(x, y)`: it gets its way when
all the other voters are unanimously opposed. -/
def AlmostDecisiveFor (G : Finset V) (x y : α) : Prop :=
  ∀ p : V → Ranking α, (∀ i ∈ G, (p i).pref x y) → (∀ i ∉ G, (p i).pref y x) →
    (F p).pref x y

/-- The coalition `G` is decisive: it is decisive for every ordered pair of distinct
alternatives. -/
def Decisive (G : Finset V) : Prop := ∀ x y : α, x ≠ y → DecisiveFor F G x y

variable {F}

lemma AlmostDecisiveFor_of_DecisiveFor {G : Finset V} {x y : α}
    (h : DecisiveFor F G x y) : AlmostDecisiveFor F G x y := fun p hp _ => h p hp

/-- **Field expansion, right**: an almost decisive coalition for `(a, b)` is decisive
for `(a, c)`, for any third alternative `c`. -/
lemma expand_right (hU : Unanimous F) (hI : IIA F) {G : Finset V} {a b c : α}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (h : AlmostDecisiveFor F G a b) :
    DecisiveFor F G a c := by
  classical
  intro p hp
  set q : V → Ranking α :=
    fun i => if i ∈ G then moveTop a (moveTop b (p i)) else moveTop b (p i) with hq
  have hqin : ∀ i ∈ G, q i = moveTop a (moveTop b (p i)) := by
    intro i hi; simp [hq, hi]
  have hqout : ∀ i ∉ G, q i = moveTop b (p i) := by
    intro i hi; simp [hq, hi]
  -- everybody prefers `b` to `c`
  have hbc : ∀ i, (q i).pref b c := by
    intro i
    by_cases hi : i ∈ G
    · rw [hqin i hi, moveTop_pref a _ (Ne.symm hab) hca]
      exact moveTop_pref_top b _ hcb
    · rw [hqout i hi]
      exact moveTop_pref_top b _ hcb
  -- `G` prefers `a` to `b`, everybody else prefers `b` to `a`
  have hGab : ∀ i ∈ G, (q i).pref a b := by
    intro i hi
    rw [hqin i hi]
    exact moveTop_pref_top a _ (Ne.symm hab)
  have hGba : ∀ i ∉ G, (q i).pref b a := by
    intro i hi
    rw [hqout i hi]
    exact moveTop_pref_top b _ hab
  have h1 : (F q).pref b c := hU q b c hbc
  have h2 : (F q).pref a b := h q hGab hGba
  have h3 : (F q).pref a c := (F q).pref_trans h2 h1
  refine (hI p q a c ?_).mpr h3
  intro i
  by_cases hi : i ∈ G
  · have hq' : (q i).pref a c := by
      rw [hqin i hi]; exact moveTop_pref_top a _ hca
    exact iff_of_true (hp i hi) hq'
  · rw [hqout i hi, moveTop_pref b _ hab hcb]

/-- **Field expansion, left**: an almost decisive coalition for `(a, b)` is decisive
for `(c, b)`, for any third alternative `c`. -/
lemma expand_left (hU : Unanimous F) (hI : IIA F) {G : Finset V} {a b c : α}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (h : AlmostDecisiveFor F G a b) :
    DecisiveFor F G c b := by
  classical
  intro p hp
  set q : V → Ranking α :=
    fun i => if i ∈ G then moveBot b (moveBot a (p i)) else moveBot a (p i) with hq
  have hqin : ∀ i ∈ G, q i = moveBot b (moveBot a (p i)) := by
    intro i hi; simp [hq, hi]
  have hqout : ∀ i ∉ G, q i = moveBot a (p i) := by
    intro i hi; simp [hq, hi]
  -- everybody prefers `c` to `a`
  have hca' : ∀ i, (q i).pref c a := by
    intro i
    by_cases hi : i ∈ G
    · rw [hqin i hi, moveBot_pref b _ hcb hab]
      exact moveBot_pref_bot a _ hca
    · rw [hqout i hi]
      exact moveBot_pref_bot a _ hca
  -- `G` prefers `a` to `b`, everybody else prefers `b` to `a`
  have hGab : ∀ i ∈ G, (q i).pref a b := by
    intro i hi
    rw [hqin i hi]
    exact moveBot_pref_bot b _ hab
  have hGba : ∀ i ∉ G, (q i).pref b a := by
    intro i hi
    rw [hqout i hi]
    exact moveBot_pref_bot a _ (Ne.symm hab)
  have h1 : (F q).pref c a := hU q c a hca'
  have h2 : (F q).pref a b := h q hGab hGba
  have h3 : (F q).pref c b := (F q).pref_trans h1 h2
  refine (hI p q c b ?_).mpr h3
  intro i
  by_cases hi : i ∈ G
  · have hq' : (q i).pref c b := by
      rw [hqin i hi]; exact moveBot_pref_bot b _ hcb
    exact iff_of_true (hp i hi) hq'
  · rw [hqout i hi, moveBot_pref a _ hca (Ne.symm hab)]

/-- From an almost decisive coalition for `(u, v)` we obtain decisiveness for `(u, w)` and for
`(w, v)`, for any third alternative `w`. -/
lemma expand_step (hU : Unanimous F) (hI : IIA F) {G : Finset V} {u v w : α}
    (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v) (h : AlmostDecisiveFor F G u v) :
    DecisiveFor F G u w ∧ DecisiveFor F G w v :=
  ⟨expand_right hU hI huv hwu hwv h, expand_left hU hI huv hwu hwv h⟩

/-- Almost decisiveness for `(u, v)` upgrades to genuine decisiveness for `(u, v)`. -/
lemma decisiveFor_of_almostDecisiveFor (hU : Unanimous F) (hI : IIA F) {G : Finset V} {u v w : α}
    (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v) (h : AlmostDecisiveFor F G u v) :
    DecisiveFor F G u v := by
  have h1 : DecisiveFor F G u w := expand_right hU hI huv hwu hwv h
  exact expand_right hU hI hwu.symm (Ne.symm huv) (Ne.symm hwv)
    (AlmostDecisiveFor_of_DecisiveFor h1)

/-- All six ordered pairs from `{a, b, c}` are covered by a coalition that is almost decisive
for `(a, b)`. -/
lemma expand_six (hU : Unanimous F) (hI : IIA F) {G : Finset V} {a b c : α}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (h : AlmostDecisiveFor F G a b) :
    AlmostDecisiveFor F G a c ∧ AlmostDecisiveFor F G c b ∧ AlmostDecisiveFor F G b c ∧
      AlmostDecisiveFor F G c a ∧ AlmostDecisiveFor F G b a := by
  have hac : AlmostDecisiveFor F G a c :=
    AlmostDecisiveFor_of_DecisiveFor (expand_right hU hI hab hca hcb h)
  have hcb' : AlmostDecisiveFor F G c b :=
    AlmostDecisiveFor_of_DecisiveFor (expand_left hU hI hab hca hcb h)
  have hbc : AlmostDecisiveFor F G b c :=
    AlmostDecisiveFor_of_DecisiveFor
      (expand_left hU hI (Ne.symm hca) (Ne.symm hab) (Ne.symm hcb) hac)
  have hca' : AlmostDecisiveFor F G c a :=
    AlmostDecisiveFor_of_DecisiveFor (expand_right hU hI hcb (Ne.symm hca) hab hcb')
  have hba : AlmostDecisiveFor F G b a :=
    AlmostDecisiveFor_of_DecisiveFor
      (expand_right hU hI (Ne.symm hcb) hab (Ne.symm hca) hbc)
  exact ⟨hac, hcb', hbc, hca', hba⟩

/-- **Contagion / field expansion lemma.**  A coalition that is almost decisive for a single
ordered pair of distinct alternatives is decisive for every ordered pair. -/
lemma decisive_of_almostDecisiveFor (hU : Unanimous F) (hI : IIA F)
    (h3 : ∀ x y : α, ∃ z : α, z ≠ x ∧ z ≠ y) {G : Finset V} {a b : α}
    (hab : a ≠ b) (h : AlmostDecisiveFor F G a b) : Decisive F G := by
  intro x y hxy
  have key : AlmostDecisiveFor F G x y := by
    by_cases hxa : x = a
    · by_cases hyb : y = b
      · rw [hxa, hyb]; exact h
      · have hya : y ≠ a := by rw [hxa] at hxy; exact Ne.symm hxy
        rw [hxa]
        exact (expand_six hU hI hab hya hyb h).1
    · by_cases hxb : x = b
      · by_cases hya : y = a
        · obtain ⟨w, hwx, hwy⟩ := h3 a b
          rw [hxb, hya]
          exact (expand_six hU hI hab hwx hwy h).2.2.2.2
        · have hyb : y ≠ b := by rw [hxb] at hxy; exact Ne.symm hxy
          rw [hxb]
          exact (expand_six hU hI hab hya hyb h).2.2.1
      · by_cases hya : y = a
        · rw [hya]
          exact (expand_six hU hI hab hxa hxb h).2.2.2.1
        · by_cases hyb : y = b
          · rw [hyb]
            exact (expand_six hU hI hab hxa hxb h).2.1
          · have hxb' : AlmostDecisiveFor F G x b := (expand_six hU hI hab hxa hxb h).2.1
            exact AlmostDecisiveFor_of_DecisiveFor
              (expand_right hU hI hxb (Ne.symm hxy) hyb hxb')
  obtain ⟨w, hwx, hwy⟩ := h3 x y
  exact decisiveFor_of_almostDecisiveFor hU hI hxy hwx hwy key

/-- **Arrow's theorem (existence of a dictator).**  A unanimous social welfare function
satisfying IIA, on at least three alternatives and finitely many voters, has a dictator. -/
theorem exists_dictator [Fintype V] (hU : Unanimous F) (hI : IIA F) (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : ∃ i : V, IsDictator F i := by
  classical
  obtain ⟨r₀⟩ : Nonempty (Ranking α) := inferInstance
  -- there are at least three alternatives
  have h3 : ∀ x y : α, ∃ z : α, z ≠ x ∧ z ≠ y := by
    intro x y
    by_contra hcon
    push_neg at hcon
    have ha : a = x ∨ a = y := by
      by_cases h' : a = x
      · exact Or.inl h'
      · exact Or.inr (hcon a h')
    have hb : b = x ∨ b = y := by
      by_cases h' : b = x
      · exact Or.inl h'
      · exact Or.inr (hcon b h')
    have hc : c = x ∨ c = y := by
      by_cases h' : c = x
      · exact Or.inl h'
      · exact Or.inr (hcon c h')
    rcases ha with h' | h' <;> rcases hb with h'' | h'' <;> rcases hc with h''' | h''' <;>
      subst_vars <;> simp_all
  -- the whole electorate is decisive
  have huniv : Decisive F (Finset.univ : Finset V) := by
    intro x y _ p hp
    exact hU p x y fun i => hp i (Finset.mem_univ i)
  have hex : ∃ n, ∃ G : Finset V, Decisive F G ∧ G.card = n :=
    ⟨_, Finset.univ, huniv, rfl⟩
  obtain ⟨G, hG, hGcard⟩ := Nat.find_spec hex
  have hmin : ∀ H : Finset V, Decisive F H → Nat.find hex ≤ H.card := fun H hH =>
    Nat.find_le ⟨H, hH, rfl⟩
  have hGne : G.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hG0
    subst hG0
    have h1 : (F fun _ => r₀).pref a b := hG a b hab _ (by simp)
    have h2 : (F fun _ => r₀).pref b a := hG b a (Ne.symm hab) _ (by simp)
    exact (F fun _ => r₀).pref_asymm h1 h2
  obtain ⟨i, hi⟩ := hGne
  by_cases hsing : G.erase i = ∅
  · -- `G = {i}`, so `i` is a dictator
    refine ⟨i, ?_⟩
    intro p x y hxy
    have hGi : G = {i} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hi, fun j hj => ?_⟩
      by_contra hji
      have : j ∈ G.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
      simp [hsing] at this
    refine hG x y hxy.2 p ?_
    intro j hj
    rw [hGi, Finset.mem_singleton] at hj
    subst hj
    exact hxy
  · -- otherwise minimality of `G` is contradicted
    exfalso
    have hG'ne : (G.erase i).Nonempty := Finset.nonempty_iff_ne_empty.mpr hsing
    have hcard2 : 2 ≤ G.card := by
      have h5 : (G.erase i).card + 1 = G.card := Finset.card_erase_add_one hi
      have h1 : 1 ≤ (G.erase i).card := Finset.card_pos.mpr hG'ne
      omega
    -- the pivotal profile: `i` ranks `a > b > c`, the rest of `G` ranks `c > a > b`, and the
    -- voters outside `G` rank `b > c > a`
    set q : V → Ranking α := fun j =>
      if j = i then top3 a b c r₀ else if j ∈ G then top3 c a b r₀ else top3 b c a r₀ with hqdef
    have hqi : q i = top3 a b c r₀ := by simp [hqdef]
    have hqG' : ∀ j, j ≠ i → j ∈ G → q j = top3 c a b r₀ := by
      intro j hj hjG; simp [hqdef, hj, hjG]
    have hqout : ∀ j, j ∉ G → q j = top3 b c a r₀ := by
      intro j hjG
      have hj : j ≠ i := by rintro rfl; exact hjG hi
      simp [hqdef, hj, hjG]
    -- everyone in `G` prefers `a` to `b`, so society does
    have hGab : ∀ j ∈ G, (q j).pref a b := by
      intro j hj
      by_cases hji : j = i
      · rw [hji, hqi]; exact top3_pref_fst_snd r₀ hab
      · rw [hqG' j hji hj]
        exact top3_pref_snd_trd r₀ (Ne.symm hac) (Ne.symm hbc) hab
    have hsocab : (F q).pref a b := hG a b hab q hGab
    by_cases hsocbc : (F q).pref b c
    · -- `{i}` is almost decisive for `(a, c)`, hence decisive: contradicts minimality
      have hsocac : (F q).pref a c := (F q).pref_trans hsocab hsocbc
      have hAD : AlmostDecisiveFor F {i} a c := by
        intro p hp hp'
        refine (hI p q a c ?_).mpr hsocac
        intro j
        by_cases hji : j = i
        · refine iff_of_true (hp j (by simp [hji])) ?_
          rw [hji, hqi]
          exact top3_pref_fst_trd r₀ hac
        · have hpj : ¬ (p j).pref a c := fun hcon =>
            (p j).pref_asymm hcon (hp' j (by simpa using hji))
          have hqj : ¬ (q j).pref a c := by
            by_cases hjG : j ∈ G
            · rw [hqG' j hji hjG]
              exact (top3 c a b r₀).pref_asymm (top3_pref_fst_snd r₀ (Ne.symm hac))
            · rw [hqout j hjG]
              exact (top3 b c a r₀).pref_asymm
                (top3_pref_snd_trd r₀ hbc (Ne.symm hab) (Ne.symm hac))
          exact iff_of_false hpj hqj
      have hdec : Decisive F ({i} : Finset V) :=
        decisive_of_almostDecisiveFor hU hI h3 hac hAD
      have hle := hmin _ hdec
      rw [Finset.card_singleton] at hle
      omega
    · -- `G.erase i` is almost decisive for `(c, b)`, hence decisive: contradicts minimality
      have hsoccb : (F q).pref c b := by
        rcases (F q).pref_total (Ne.symm hbc) with h' | h'
        · exact h'
        · exact absurd h' hsocbc
      have hAD : AlmostDecisiveFor F (G.erase i) c b := by
        intro p hp hp'
        refine (hI p q c b ?_).mpr hsoccb
        intro j
        by_cases hjG : j ∈ G.erase i
        · have hji : j ≠ i := (Finset.mem_erase.mp hjG).1
          have hjG' : j ∈ G := (Finset.mem_erase.mp hjG).2
          refine iff_of_true (hp j hjG) ?_
          rw [hqG' j hji hjG']
          exact top3_pref_fst_trd r₀ (Ne.symm hbc)
        · have hpj : ¬ (p j).pref c b := fun hcon =>
            (p j).pref_asymm hcon (hp' j hjG)
          have hqj : ¬ (q j).pref c b := by
            by_cases hji : j = i
            · rw [hji, hqi]
              exact (top3 a b c r₀).pref_asymm (top3_pref_snd_trd r₀ hab hac hbc)
            · have hjG' : j ∉ G := fun hmem => hjG (Finset.mem_erase.mpr ⟨hji, hmem⟩)
              rw [hqout j hjG']
              exact (top3 b c a r₀).pref_asymm (top3_pref_fst_snd r₀ hbc)
          exact iff_of_false hpj hqj
      have hdec : Decisive F (G.erase i) :=
        decisive_of_almostDecisiveFor hU hI h3 (Ne.symm hbc) hAD
      have h4 := hmin _ hdec
      have h5 : (G.erase i).card + 1 = G.card := Finset.card_erase_add_one hi
      omega

/-- **Arrow's impossibility theorem.**  With at least three alternatives (`a`, `b`, `c`
pairwise distinct) and finitely many voters, no ranked voting rule `F` is simultaneously
unanimous, independent of irrelevant alternatives, and non-dictatorial. -/
theorem arrow_impossibility {V α : Type*} [Fintype V] (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (F : (V → Ranking α) → Ranking α) :
    ¬ (Unanimous F ∧ IIA F ∧ ∀ i : V, ¬ IsDictator F i) := by
  rintro ⟨hU, hI, hnd⟩
  obtain ⟨i, hi⟩ := exists_dictator hU hI a b c hab hac hbc
  exact hnd i hi

/-- Non-vacuity check: dropping non-dictatorship the axioms *are* satisfiable — the projection
onto voter `i` (the dictatorship of `i`) is unanimous, satisfies IIA, and has `i` as a
dictator. -/
theorem dictatorship_unanimous_iia {V α : Type*} (i : V) :
    Unanimous (fun p : V → Ranking α => p i) ∧ IIA (fun p : V → Ranking α => p i) ∧
      IsDictator (fun p : V → Ranking α => p i) i :=
  ⟨fun _ _ _ h => h i, fun _ _ _ _ h => h i, fun _ _ _ h => h⟩

end Arrow

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

