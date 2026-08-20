import Mathlib
import RequestProject.ArrowImpossibility

/-!
# Arrow impossibility, phrased with `Fintype`

`RequestProject.ArrowImpossibility` is deliberately self-contained (it uses no imports at
all), so it expresses finiteness of the voter set by `Frontier.FinitelyMany`.  This file
records the same statement with Mathlib's `Fintype` hypothesis.
-/

namespace Frontier

universe v

theorem finitelyMany_of_fintype {V : Type v} [Fintype V] : FinitelyMany V :=
  ⟨Finset.univ.toList, fun x => by simp⟩

/-- **Arrow's impossibility theorem** for three alternatives and a finite type of voters:
no social welfare function is unanimous, independent of irrelevant alternatives and
non-dictatorial. -/
theorem arrow_impossibility_fintype {V : Type v} [Fintype V] :
    ¬ ∃ F : (V → Ranking (Fin 3)) → Ranking (Fin 3),
        Unanimous F ∧ IIA F ∧ (∀ i : V, ¬ IsDictator F i) :=
  arrow_impossibility finitelyMany_of_fintype

end Frontier

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u v

/-! ## Rankings (strict linear orders) -/

/-- A *ranking* of `α`: a strict linear order, described by its strict part `lt`. -/
structure Ranking (α : Type u) where
  /-- The strict preference relation: `lt x y` means "`x` is strictly preferred to `y`". -/
  lt : α → α → Prop
  /-- Transitivity. -/
  tr : ∀ {x y z : α}, lt x y → lt y z → lt x z
  /-- Totality: distinct alternatives are comparable. -/
  tot : ∀ x y : α, x ≠ y → lt x y ∨ lt y x
  /-- Asymmetry. -/
  asym : ∀ {x y : α}, lt x y → ¬ lt y x

namespace Ranking

variable {α : Type u} (R : Ranking α)

theorem irrefl (x : α) : ¬ R.lt x x := fun h => R.asym h h

theorem ne_of_lt {x y : α} (h : R.lt x y) : x ≠ y := by
  intro he; rw [he] at h; exact R.irrefl y h

theorem lt_iff_not_lt {x y : α} (hxy : x ≠ y) : R.lt y x ↔ ¬ R.lt x y :=
  ⟨fun h hc => R.asym h hc, fun h => (R.tot x y hxy).resolve_left h⟩

/-- The ranking induced by an injective "score" function into `Nat` (smaller is better). -/
def ofRank (r : α → Nat) (hr : ∀ x y, r x = r y → x = y) : Ranking α where
  lt := fun x y => r x < r y
  tr := fun h1 h2 => Nat.lt_trans h1 h2
  tot := fun x y hxy => by
    have h : r x ≠ r y := fun he => hxy (hr x y he)
    omega
  asym := fun h => Nat.lt_asymm h

theorem ofRank_lt (r : α → Nat) (hr : ∀ x y, r x = r y → x = y) (x y : α) :
    (ofRank r hr).lt x y ↔ r x < r y := Iff.rfl

end Ranking

/-! ## The rankings of three alternatives -/

/-- Score function on `Fin 3` placing `a` first, `b` second, and the remaining one last. -/
def triR (a b x : Fin 3) : Nat := if x = a then 0 else if x = b then 1 else 2

/-- Injectivity, spelled out so that it is decidable. -/
def Inj3 (r : Fin 3 → Nat) : Prop := ∀ x y : Fin 3, r x = r y → x = y

instance (r : Fin 3 → Nat) : Decidable (Inj3 r) := by
  unfold Inj3; infer_instance

/-- The ranking of the three alternatives that puts `a` first, `b` second and the
remaining alternative last (for `a ≠ b`). -/
def tri (a b : Fin 3) : Ranking (Fin 3) :=
  if h : Inj3 (triR a b) then Ranking.ofRank (triR a b) h
  else Ranking.ofRank (fun x : Fin 3 => x.val) (fun _ _ h => Fin.eq_of_val_eq h)

theorem triR_inj (a b : Fin 3) (hab : a ≠ b) : Inj3 (triR a b) := by
  revert hab; revert a b; decide

/-- Complete description of the strict preferences of `tri a b`, where `c` is the third
alternative. -/
theorem tri_lt_iff (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x y : Fin 3) :
    (tri a b).lt x y ↔ ((x = a ∧ y ≠ a) ∨ (x = b ∧ y = c)) := by
  rw [tri, dif_pos (triR_inj a b hab), Ranking.ofRank_lt]
  revert hab hac hbc; revert a b c x y; decide

/-! ## Social welfare functions -/

section Defs

variable {α : Type u} {V : Type v}

/-- Weak Pareto / unanimity: a strict preference shared by all voters is the social
preference. -/
def Unanimous (F : (V → Ranking α) → Ranking α) : Prop :=
  ∀ (P : V → Ranking α) (x y : α), (∀ i, (P i).lt x y) → (F P).lt x y

/-- Independence of irrelevant alternatives: the social preference between `x` and `y`
depends only on the individual preferences between `x` and `y`. -/
def IIA (F : (V → Ranking α) → Ranking α) : Prop :=
  ∀ (P Q : V → Ranking α) (x y : α),
    (∀ i, ((P i).lt x y ↔ (Q i).lt x y) ∧ ((P i).lt y x ↔ (Q i).lt y x)) →
      ((F P).lt x y ↔ (F Q).lt x y)

/-- Voter `i` is decisive for the ordered pair `(x, y)`. -/
def Decisive (F : (V → Ranking α) → Ranking α) (i : V) (x y : α) : Prop :=
  ∀ P : V → Ranking α, (P i).lt x y → (F P).lt x y

/-- Voter `i` is a dictator: the social ranking always follows `i`'s ranking. -/
def IsDictator (F : (V → Ranking α) → Ranking α) (i : V) : Prop :=
  ∀ (P : V → Ranking α) (x y : α), (P i).lt x y → (F P).lt x y

/-- `V` is finite: some list contains every element. -/
def FinitelyMany (V : Type v) : Prop := ∃ l : List V, ∀ x : V, x ∈ l

/-- Since preferences are rankings, agreement on `x < y` alone already gives the full
hypothesis of IIA for the pair `{x, y}`. -/
theorem iia_pair {F : (V → Ranking α) → Ranking α} (hiia : IIA F) (P Q : V → Ranking α)
    (x y : α) (hxy : x ≠ y) (h : ∀ i, ((P i).lt x y ↔ (Q i).lt x y)) :
    ((F P).lt x y ↔ (F Q).lt x y) := by
  refine hiia P Q x y (fun i => ⟨h i, ?_⟩)
  rw [(P i).lt_iff_not_lt hxy, (Q i).lt_iff_not_lt hxy, h i]

end Defs

/-! ## A combinatorial pivot lemma -/

/-- If a membership-invariant predicate on coalitions fails for the empty coalition but
holds for some coalition, then there is a coalition `S` and a voter `i ∉ S` for which
adding `i` to `S` flips the predicate. -/
theorem exists_pivot {V : Type v} (T : List V → Prop)
    (hinv : ∀ u w : List V, (∀ x, x ∈ u ↔ x ∈ w) → (T u ↔ T w)) (h0 : ¬ T []) :
    ∀ s : List V, T s → ∃ (S : List V) (i : V), i ∉ S ∧ ¬ T S ∧ T (i :: S) := by
  intro s
  induction s with
  | nil => intro h; exact absurd h h0
  | cons a t ih =>
      intro h
      by_cases ht : T t
      · exact ih ht
      · by_cases ha : a ∈ t
        · refine absurd ((hinv (a :: t) t ?_).mp h) ht
          intro x
          rw [List.mem_cons]
          constructor
          · rintro (rfl | hx)
            · exact ha
            · exact hx
          · exact Or.inr
        · exact ⟨t, a, ha, ht, h⟩

/-! ## Profiles used in the proof -/

section Profiles

variable {V : Type v}

open Classical in
/-- The profile in which the voters of `S` rank `b` first (then `a`, then `c`) and all
other voters rank `b` last (after `a`, then `c`). -/
noncomputable def bTop (a b c : Fin 3) (S : List V) : V → Ranking (Fin 3) :=
  fun j => if j ∈ S then tri b a else tri a c

theorem bTop_mem {a b c : Fin 3} {S : List V} {j : V} (h : j ∈ S) :
    bTop a b c S j = tri b a := by
  simp [bTop, h]

theorem bTop_not_mem {a b c : Fin 3} {S : List V} {j : V} (h : j ∉ S) :
    bTop a b c S j = tri a c := by
  simp [bTop, h]

open Classical in
/-- From a profile in which `b` is extremal for every voter, the profile obtained by
keeping `b`'s position and ranking `c` above `a`. -/
noncomputable def swapProfile (a b c : Fin 3) (P : V → Ranking (Fin 3)) :
    V → Ranking (Fin 3) :=
  fun j => if (P j).lt b a then tri b c else tri c a

theorem swapProfile_top {a b c : Fin 3} {P : V → Ranking (Fin 3)} {j : V}
    (h : (P j).lt b a) : swapProfile a b c P j = tri b c := by
  simp [swapProfile, h]

theorem swapProfile_bot {a b c : Fin 3} {P : V → Ranking (Fin 3)} {j : V}
    (h : ¬ (P j).lt b a) : swapProfile a b c P j = tri c a := by
  simp [swapProfile, h]

open Classical in
/-- The profile used to show that the pivotal voter `i` is decisive for `(a, c)`. -/
noncomputable def pivProfile (a b c : Fin 3) (S : List V) (i : V)
    (Q : V → Ranking (Fin 3)) : V → Ranking (Fin 3) :=
  fun j =>
    if j = i then tri a b
    else if j ∈ S then (if (Q j).lt a c then tri b a else tri b c)
    else (if (Q j).lt a c then tri a c else tri c a)

theorem pivProfile_self {a b c : Fin 3} {S : List V} {i : V} {Q : V → Ranking (Fin 3)} :
    pivProfile a b c S i Q i = tri a b := by
  simp [pivProfile]

theorem pivProfile_mem_pos {a b c : Fin 3} {S : List V} {i j : V} {Q : V → Ranking (Fin 3)}
    (hj : j ≠ i) (hjS : j ∈ S) (hq : (Q j).lt a c) :
    pivProfile a b c S i Q j = tri b a := by
  simp [pivProfile, hj, hjS, hq]

theorem pivProfile_mem_neg {a b c : Fin 3} {S : List V} {i j : V} {Q : V → Ranking (Fin 3)}
    (hj : j ≠ i) (hjS : j ∈ S) (hq : ¬ (Q j).lt a c) :
    pivProfile a b c S i Q j = tri b c := by
  simp [pivProfile, hj, hjS, hq]

theorem pivProfile_not_mem_pos {a b c : Fin 3} {S : List V} {i j : V}
    {Q : V → Ranking (Fin 3)} (hj : j ≠ i) (hjS : j ∉ S) (hq : (Q j).lt a c) :
    pivProfile a b c S i Q j = tri a c := by
  simp [pivProfile, hj, hjS, hq]

theorem pivProfile_not_mem_neg {a b c : Fin 3} {S : List V} {i j : V}
    {Q : V → Ranking (Fin 3)} (hj : j ≠ i) (hjS : j ∉ S) (hq : ¬ (Q j).lt a c) :
    pivProfile a b c S i Q j = tri c a := by
  simp [pivProfile, hj, hjS, hq]

open Classical in
/-- The profile where voter `p` has ranking `R1` and everybody else has ranking `R2`. -/
noncomputable def twoProfile (R1 R2 : Ranking (Fin 3)) (p : V) : V → Ranking (Fin 3) :=
  fun j => if j = p then R1 else R2

theorem twoProfile_self {R1 R2 : Ranking (Fin 3)} {p : V} : twoProfile R1 R2 p p = R1 := by
  simp [twoProfile]

theorem twoProfile_other {R1 R2 : Ranking (Fin 3)} {p j : V} (h : j ≠ p) :
    twoProfile R1 R2 p j = R2 := by
  simp [twoProfile, h]

end Profiles

/-! ## Arrow's theorem for three alternatives -/

section Arrow

variable {V : Type v} {F : (V → Ranking (Fin 3)) → Ranking (Fin 3)}

/-- If every voter puts `b` at the top or at the bottom, society cannot rank `b` strictly
between `a` and `c`. -/
theorem no_middle (huna : Unanimous F) (hiia : IIA F) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (P : V → Ranking (Fin 3))
    (hP : ∀ j, ((P j).lt b a ∧ (P j).lt b c) ∨ ((P j).lt a b ∧ (P j).lt c b)) :
    ¬ ((F P).lt a b ∧ (F P).lt b c) := by
  have hba : b ≠ a := hab.symm
  have hca : c ≠ a := hac.symm
  have hcb : c ≠ b := hbc.symm
  have L4 := tri_lt_iff b c a hbc hba hca
  have L5 := tri_lt_iff c a b hca hcb hab
  rintro ⟨h1, h2⟩
  have hcase : ∀ j, ((P j).lt b a ∧ (P j).lt b c ∧ swapProfile a b c P j = tri b c) ∨
      ((P j).lt a b ∧ (P j).lt c b ∧ swapProfile a b c P j = tri c a) := by
    intro j
    rcases hP j with ⟨u, w⟩ | ⟨u, w⟩
    · exact Or.inl ⟨u, w, swapProfile_top u⟩
    · exact Or.inr ⟨u, w, swapProfile_bot ((P j).asym u)⟩
  have hab' : (F (swapProfile a b c P)).lt a b := by
    refine (iia_pair hiia _ P a b hab ?_).mpr h1
    intro j
    rcases hcase j with ⟨u, w, e⟩ | ⟨u, w, e⟩ <;> rw [e]
    · simp only [L4]
      have a1 : ¬ (P j).lt a b := (P j).asym u
      simp [hab, hac, hba, a1]
    · simp only [L5]
      simp [hac, hbc, u]
  have hbc' : (F (swapProfile a b c P)).lt b c := by
    refine (iia_pair hiia _ P b c hbc ?_).mpr h2
    intro j
    rcases hcase j with ⟨u, w, e⟩ | ⟨u, w, e⟩ <;> rw [e]
    · simp only [L4]
      simp [hbc, hca, hcb, w]
    · simp only [L5]
      have a2 : ¬ (P j).lt b c := (P j).asym w
      simp [hbc, hba, hcb, a2]
  have hcaF : (F (swapProfile a b c P)).lt c a := by
    refine huna _ c a ?_
    intro j
    rcases hcase j with ⟨u, w, e⟩ | ⟨u, w, e⟩ <;> rw [e]
    · simp only [L4]
      simp [hab, hcb]
    · simp only [L5]
      simp [hab, hac, hca]
  exact (F (swapProfile a b c P)).asym hcaF ((F (swapProfile a b c P)).tr hab' hbc')

/-- Extremal lemma: if every voter ranks `b` at the top or at the bottom, then so does
society. -/
theorem extremal (huna : Unanimous F) (hiia : IIA F) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (P : V → Ranking (Fin 3))
    (hP : ∀ j, ((P j).lt b a ∧ (P j).lt b c) ∨ ((P j).lt a b ∧ (P j).lt c b)) :
    ((F P).lt b a ∧ (F P).lt b c) ∨ ((F P).lt a b ∧ (F P).lt c b) := by
  have n1 := no_middle huna hiia hab hac hbc P hP
  have n2 := no_middle huna hiia (a := c) (b := b) (c := a) hbc.symm hac.symm hab.symm P
    (by
      intro j
      rcases hP j with ⟨u, w⟩ | ⟨u, w⟩
      · exact Or.inl ⟨w, u⟩
      · exact Or.inr ⟨w, u⟩)
  rcases (F P).tot b a hab.symm with hba | hab₂
  · rcases (F P).tot b c hbc with hbc₂ | hcb
    · exact Or.inl ⟨hba, hbc₂⟩
    · exact absurd ⟨hcb, hba⟩ n2
  · rcases (F P).tot b c hbc with hbc₂ | hcb
    · exact absurd ⟨hab₂, hbc₂⟩ n1
    · exact Or.inr ⟨hab₂, hcb⟩

/-- **Key lemma.** For any three distinct alternatives `a`, `b`, `c` there is a voter who
is decisive for the ordered pair `(a, c)`. -/
theorem exists_decisive (hV : FinitelyMany V) (huna : Unanimous F) (hiia : IIA F)
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ i : V, Decisive F i a c := by
  obtain ⟨l, hl⟩ := hV
  have hba : b ≠ a := hab.symm
  have hca : c ≠ a := hac.symm
  have hcb : c ≠ b := hbc.symm
  have L1 := tri_lt_iff a b c hab hac hbc
  have L2 := tri_lt_iff a c b hac hab hcb
  have L3 := tri_lt_iff b a c hba hbc hac
  have L4 := tri_lt_iff b c a hbc hba hca
  have L5 := tri_lt_iff c a b hca hcb hab
  -- in every `bTop` profile, `b` is extremal for each voter
  have hext : ∀ S : List V, ∀ j : V,
      (((bTop a b c S) j).lt b a ∧ ((bTop a b c S) j).lt b c) ∨
      (((bTop a b c S) j).lt a b ∧ ((bTop a b c S) j).lt c b) := by
    intro S j
    by_cases hj : j ∈ S
    · rw [bTop_mem hj]
      simp only [L3]
      simp [hab, hac, hbc, hba, hca, hcb]
    · rw [bTop_not_mem hj]
      simp only [L2]
      simp [hab, hac, hbc, hba, hca, hcb]
  let T : List V → Prop := fun S =>
    (F (bTop a b c S)).lt b a ∧ (F (bTop a b c S)).lt b c
  have hTinv : ∀ u w : List V, (∀ x, x ∈ u ↔ x ∈ w) → (T u ↔ T w) := by
    intro u w huw
    have heq : bTop a b c u = bTop a b c w := by
      funext j
      by_cases hj : j ∈ u
      · rw [bTop_mem hj, bTop_mem ((huw j).mp hj)]
      · rw [bTop_not_mem hj, bTop_not_mem (fun hc => hj ((huw j).mpr hc))]
    exact ⟨fun h => ⟨heq ▸ h.1, heq ▸ h.2⟩, fun h => ⟨heq ▸ h.1, heq ▸ h.2⟩⟩
  have hT0 : ¬ T ([] : List V) := by
    have h1 : (F (bTop a b c ([] : List V))).lt a b := by
      refine huna _ a b ?_
      intro j
      rw [bTop_not_mem (S := ([] : List V)) (List.not_mem_nil)]
      simp only [L2]
      simp [hac, hba]
    intro hc
    exact (F (bTop a b c ([] : List V))).asym h1 hc.1
  have hT1 : T l := by
    constructor <;>
    · refine huna _ _ _ ?_
      intro j
      rw [bTop_mem (hl j)]
      simp only [L3]
      simp [hab, hac, hba, hcb]
  obtain ⟨S, i, hiS, hnS, hins⟩ := exists_pivot T hTinv hT0 l hT1
  have hbot : (F (bTop a b c S)).lt a b ∧ (F (bTop a b c S)).lt c b := by
    rcases extremal huna hiia hab hac hbc (bTop a b c S) (hext S) with h | h
    · exact absurd h hnS
    · exact h
  refine ⟨i, ?_⟩
  intro Q hQ
  -- `R` agrees with `bTop S` on the pair `(a, b)`
  have hRab : (F (pivProfile a b c S i Q)).lt a b := by
    refine (iia_pair hiia _ (bTop a b c S) a b hab ?_).mpr hbot.1
    intro j
    by_cases hj : j = i
    · subst hj
      rw [pivProfile_self, bTop_not_mem hiS]
      simp only [L1, L2]
      simp [hab, hac, hbc, hba]
    · by_cases hjS : j ∈ S
      · rw [bTop_mem hjS]
        by_cases hq : (Q j).lt a c
        · rw [pivProfile_mem_pos hj hjS hq]
        · rw [pivProfile_mem_neg hj hjS hq]
          simp only [L3, L4]
          simp [hab, hac, hbc, hba]
      · rw [bTop_not_mem hjS]
        by_cases hq : (Q j).lt a c
        · rw [pivProfile_not_mem_pos hj hjS hq]
        · rw [pivProfile_not_mem_neg hj hjS hq]
          simp only [L2, L5]
          simp [hac, hbc, hba]
  -- `R` agrees with `bTop (i :: S)` on the pair `(b, c)`
  have hRbc : (F (pivProfile a b c S i Q)).lt b c := by
    refine (iia_pair hiia _ (bTop a b c (i :: S)) b c hbc ?_).mpr hins.2
    intro j
    by_cases hj : j = i
    · subst hj
      rw [pivProfile_self, bTop_mem (S := j :: S) (by simp)]
      simp only [L1, L3]
      simp [hba, hca, hcb]
    · by_cases hjS : j ∈ S
      · rw [bTop_mem (S := i :: S) (by simp [hjS])]
        by_cases hq : (Q j).lt a c
        · rw [pivProfile_mem_pos hj hjS hq]
        · rw [pivProfile_mem_neg hj hjS hq]
          simp only [L3, L4]
          simp [hbc, hba, hca, hcb]
      · rw [bTop_not_mem (S := i :: S) (by simp [hj, hjS])]
        by_cases hq : (Q j).lt a c
        · rw [pivProfile_not_mem_pos hj hjS hq]
        · rw [pivProfile_not_mem_neg hj hjS hq]
          simp only [L2, L5]
          simp [hbc, hba, hca, hcb]
  have hRac : (F (pivProfile a b c S i Q)).lt a c :=
    (F (pivProfile a b c S i Q)).tr hRab hRbc
  -- `R` agrees with `Q` on the pair `(a, c)`
  refine (iia_pair hiia _ Q a c hac ?_).mp hRac
  intro j
  by_cases hj : j = i
  · subst hj
    rw [pivProfile_self]
    simp only [L1]
    simp [hab, hca, hQ]
  · by_cases hjS : j ∈ S
    · by_cases hq : (Q j).lt a c
      · rw [pivProfile_mem_pos hj hjS hq]
        simp only [L3]
        simp [hab, hcb, hq]
      · rw [pivProfile_mem_neg hj hjS hq]
        simp only [L4]
        simp [hab, hac, hca, hcb, hq]
    · by_cases hq : (Q j).lt a c
      · rw [pivProfile_not_mem_pos hj hjS hq]
        simp only [L2]
        simp [hac, hca, hcb, hq]
      · rw [pivProfile_not_mem_neg hj hjS hq]
        simp only [L5]
        simp [hac, hcb, hq]

/-- Two voters decisive for opposite ordered pairs must be the same voter. -/
theorem flip_eq {p q : V} {x y : Fin 3} (hxy : x ≠ y)
    (hp : Decisive F p x y) (hq : Decisive F q y x) : p = q := by
  refine Classical.byContradiction (fun hpq => ?_)
  obtain ⟨z, hzx, hzy⟩ : ∃ z : Fin 3, z ≠ x ∧ z ≠ y := by
    clear hp hq; revert hxy; revert x y; decide
  have hyx : y ≠ x := hxy.symm
  have hxz : x ≠ z := hzx.symm
  have hyz : y ≠ z := hzy.symm
  have Lxy := tri_lt_iff x y z hxy hxz hyz
  have Lyx := tri_lt_iff y x z hyx hyz hxz
  have h1 : (F (twoProfile (tri x y) (tri y x) p)).lt x y := by
    refine hp _ ?_
    rw [twoProfile_self]
    simp only [Lxy]
    simp [hxy, hyx, hyz]
  have h2 : (F (twoProfile (tri x y) (tri y x) p)).lt y x := by
    refine hq _ ?_
    rw [twoProfile_other (Ne.symm hpq)]
    simp only [Lyx]
    simp [hxy, hyx, hxz]
  exact (F (twoProfile (tri x y) (tri y x) p)).asym h1 h2

/-- If `p` is decisive for `(x, y)` and `q` is decisive for `(y, z)`, then `p = q`. -/
theorem triangle_eq (huna : Unanimous F) {p q : V} {x y z : Fin 3}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hp : Decisive F p x y) (hq : Decisive F q y z) : p = q := by
  refine Classical.byContradiction (fun hpq => ?_)
  have hyx : y ≠ x := hxy.symm
  have hzx : z ≠ x := hxz.symm
  have hzy : z ≠ y := hyz.symm
  have Lzxy := tri_lt_iff z x y hzx hzy hxy
  have Lyzx := tri_lt_iff y z x hyz hyx hzx
  have h1 : (F (twoProfile (tri y z) (tri z x) q)).lt x y := by
    refine hp _ ?_
    rw [twoProfile_other hpq]
    simp only [Lzxy]
    simp [hxz, hyz]
  have h2 : (F (twoProfile (tri y z) (tri z x) q)).lt y z := by
    refine hq _ ?_
    rw [twoProfile_self]
    simp only [Lyzx]
    simp [hzx, hyz, hzy]
  have h3 : (F (twoProfile (tri y z) (tri z x) q)).lt z x := by
    refine huna _ z x ?_
    intro j
    by_cases hj : j = q
    · subst hj
      rw [twoProfile_self]
      simp only [Lyzx]
      simp [hxy, hzy]
    · rw [twoProfile_other hj]
      simp only [Lzxy]
      simp [hxy, hxz, hzx]
  exact (F (twoProfile (tri y z) (tri z x) q)).asym h3
    ((F (twoProfile (tri y z) (tri z x) q)).tr h1 h2)

/-- **Arrow's theorem (three alternatives).** A unanimous social welfare function
satisfying IIA on three alternatives, with finitely many voters, has a dictator. -/
theorem exists_dictator (hV : FinitelyMany V) (huna : Unanimous F) (hiia : IIA F) :
    ∃ i : V, IsDictator F i := by
  obtain ⟨p, h01⟩ := exists_decisive hV huna hiia (a := (0 : Fin 3)) (b := 2) (c := 1)
    (by decide) (by decide) (by decide)
  obtain ⟨q10, h10⟩ := exists_decisive hV huna hiia (a := (1 : Fin 3)) (b := 2) (c := 0)
    (by decide) (by decide) (by decide)
  obtain ⟨q12, h12⟩ := exists_decisive hV huna hiia (a := (1 : Fin 3)) (b := 0) (c := 2)
    (by decide) (by decide) (by decide)
  obtain ⟨q21, h21⟩ := exists_decisive hV huna hiia (a := (2 : Fin 3)) (b := 0) (c := 1)
    (by decide) (by decide) (by decide)
  obtain ⟨q20, h20⟩ := exists_decisive hV huna hiia (a := (2 : Fin 3)) (b := 1) (c := 0)
    (by decide) (by decide) (by decide)
  obtain ⟨q02, h02⟩ := exists_decisive hV huna hiia (a := (0 : Fin 3)) (b := 1) (c := 2)
    (by decide) (by decide) (by decide)
  have h10p : Decisive F p 1 0 := by
    have e10 : q10 = p := flip_eq (by decide) h10 h01
    rw [← e10]; exact h10
  have h12p : Decisive F p 1 2 := by
    have e12 : p = q12 := triangle_eq huna (x := (0 : Fin 3)) (y := 1) (z := 2)
      (by decide) (by decide) (by decide) h01 h12
    rw [e12]; exact h12
  have h21p : Decisive F p 2 1 := by
    have e21 : p = q21 := flip_eq (by decide) h12p h21
    rw [e21]; exact h21
  have h20p : Decisive F p 2 0 := by
    have e20 : p = q20 := triangle_eq huna (x := (1 : Fin 3)) (y := 2) (z := 0)
      (by decide) (by decide) (by decide) h12p h20
    rw [e20]; exact h20
  have h02p : Decisive F p 0 2 := by
    have e02 : p = q02 := flip_eq (by decide) h20p h02
    rw [e02]; exact h02
  refine ⟨p, ?_⟩
  intro P x y hxy
  have hne : x ≠ y := (P p).ne_of_lt hxy
  have hcases : (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 0) ∨ (x = 1 ∧ y = 2) ∨
      (x = 2 ∧ y = 0) ∨ (x = 2 ∧ y = 1) := by
    clear hxy; revert hne; revert x y; decide
  rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
    subst hx <;> subst hy
  · exact h01 P hxy
  · exact h02p P hxy
  · exact h10p P hxy
  · exact h12p P hxy
  · exact h20p P hxy
  · exact h21p P hxy

end Arrow

/-- The three conditions are not vacuously incompatible: dropping non-dictatorship
leaves a rule, namely the dictatorship of voter `i`, which is unanimous and satisfies
independence of irrelevant alternatives. -/
theorem dictatorship_unanimous_and_IIA {V : Type v} (i : V) :
    Unanimous (fun P : V → Ranking (Fin 3) => P i) ∧
      IIA (fun P : V → Ranking (Fin 3) => P i) ∧
      IsDictator (fun P : V → Ranking (Fin 3) => P i) i :=
  ⟨fun _ _ _ h => h i, fun _ _ _ _ h => (h i).1, fun _ _ _ h => h⟩

/-- **Arrow's impossibility theorem** (base case: three alternatives, finitely many
voters). No social welfare function aggregating individual rankings of three
alternatives into a social ranking is simultaneously unanimous, independent of
irrelevant alternatives, and non-dictatorial. -/
theorem arrow_impossibility {V : Type v} (hV : FinitelyMany V) :
    ¬ ∃ F : (V → Ranking (Fin 3)) → Ranking (Fin 3),
        Unanimous F ∧ IIA F ∧ (∀ i : V, ¬ IsDictator F i) := by
  rintro ⟨F, hu, hi, hnd⟩
  obtain ⟨p, hp⟩ := exists_dictator hV hu hi
  exact hnd p hp

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

