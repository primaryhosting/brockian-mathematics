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

/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*} {n : ℕ}

/-! ## Rankings and profiles -/

/-- `r` is a strict ranking (irreflexive, transitive, total) of the alternatives. -/
structure IsRanking (r : A → A → Prop) : Prop where
  asymm : ∀ x y, r x y → ¬ r y x
  trans' : ∀ x y z, r x y → r y z → r x z
  total : ∀ x y, x ≠ y → r x y ∨ r y x

lemma IsRanking.irrefl {r : A → A → Prop} (h : IsRanking r) (x : A) : ¬ r x x :=
  fun hx => h.asymm x x hx hx

lemma IsRanking.ne' {r : A → A → Prop} (h : IsRanking r) {x y : A} (hxy : r x y) : x ≠ y := by
  rintro rfl; exact h.irrefl x hxy

/-- A profile assigns a ranking of the alternatives to each of the `n` voters. -/
def IsProfile (P : Fin n → A → A → Prop) : Prop := ∀ i, IsRanking (P i)

/-- Voter `d` is a dictator for the aggregation rule `F`. -/
def IsDictator (F : (Fin n → A → A → Prop) → (A → A → Prop)) (d : Fin n) : Prop :=
  ∀ P, IsProfile P → ∀ x y, P d x y → F P x y

/-- A social welfare function: an aggregation rule which is rational (the social preference is
again a ranking), unanimous (Pareto) and independent of irrelevant alternatives. -/
structure SWF (A : Type*) (n : ℕ) where
  /-- the aggregation rule -/
  F : (Fin n → A → A → Prop) → (A → A → Prop)
  /-- the social preference is again a ranking -/
  rational : ∀ P, IsProfile P → IsRanking (F P)
  /-- unanimity -/
  pareto : ∀ P, IsProfile P → ∀ x y, (∀ i, P i x y) → F P x y
  /-- independence of irrelevant alternatives -/
  iia : ∀ P Q, IsProfile P → IsProfile Q → ∀ x y,
    (∀ i, (P i x y ↔ Q i x y) ∧ (P i y x ↔ Q i y x)) → (F P x y ↔ F Q x y)

/-! ## Building rankings -/

/-- Refine a ranking `r` by a priority function `rk` (lexicographic order). -/
def byRank (rk : A → ℕ) (r : A → A → Prop) : A → A → Prop :=
  fun x y => rk x < rk y ∨ (rk x = rk y ∧ r x y)

lemma byRank_of_lt {rk : A → ℕ} {r : A → A → Prop} {x y : A} (h : rk x < rk y) :
    byRank rk r x y := Or.inl h

lemma byRank_not_of_lt {rk : A → ℕ} {r : A → A → Prop} {x y : A} (h : rk x < rk y) :
    ¬ byRank rk r y x := by
  rintro (h1 | ⟨h1, -⟩) <;> omega

lemma byRank_iff_of_eq {rk : A → ℕ} {r : A → A → Prop} {x y : A} (h : rk x = rk y) :
    byRank rk r x y ↔ r x y := by
  constructor
  · rintro (h1 | ⟨-, h2⟩)
    · omega
    · exact h2
  · exact fun h2 => Or.inr ⟨h, h2⟩

lemma isRanking_byRank (rk : A → ℕ) {r : A → A → Prop} (hr : IsRanking r) :
    IsRanking (byRank rk r) where
  asymm := by
    rintro x y (h | ⟨h, hr1⟩) (h' | ⟨h', hr2⟩)
    · omega
    · omega
    · omega
    · exact hr.asymm _ _ hr1 hr2
  trans' := by
    rintro x y z (h | ⟨h, hr1⟩) (h' | ⟨h', hr2⟩)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, hr.trans' _ _ _ hr1 hr2⟩
  total := by
    intro x y hxy
    rcases lt_trichotomy (rk x) (rk y) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases hr.total x y hxy with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inr (Or.inl h)

/-- Every type carries a ranking. -/
lemma exists_ranking (A : Type*) : ∃ r : A → A → Prop, IsRanking r := by
  refine ⟨WellOrderingRel, ?_, ?_, ?_⟩
  · exact fun x y h h' => asymm h h'
  · exact fun x y z h h' => _root_.trans h h'
  · intro x y hxy
    rcases trichotomous_of WellOrderingRel x y with h | h | h
    · exact Or.inl h
    · exact absurd h hxy
    · exact Or.inr h

open Classical in
/-- `r` with `b` moved to the top. -/
noncomputable def topOrd (b : A) (r : A → A → Prop) : A → A → Prop :=
  byRank (fun z => if z = b then 0 else 1) r

open Classical in
/-- `r` with `b` moved to the bottom. -/
noncomputable def botOrd (b : A) (r : A → A → Prop) : A → A → Prop :=
  byRank (fun z => if z = b then 1 else 0) r

lemma isRanking_topOrd (b : A) {r : A → A → Prop} (hr : IsRanking r) : IsRanking (topOrd b r) :=
  isRanking_byRank _ hr

lemma isRanking_botOrd (b : A) {r : A → A → Prop} (hr : IsRanking r) : IsRanking (botOrd b r) :=
  isRanking_byRank _ hr

lemma topOrd_top {b x : A} (r : A → A → Prop) (h : x ≠ b) : topOrd b r b x := by
  classical
  apply byRank_of_lt
  simp [h]

lemma topOrd_not_top {b x : A} (r : A → A → Prop) (h : x ≠ b) : ¬ topOrd b r x b := by
  classical
  apply byRank_not_of_lt
  simp [h]

lemma botOrd_bot {b x : A} (r : A → A → Prop) (h : x ≠ b) : botOrd b r x b := by
  classical
  apply byRank_of_lt
  simp [h]

lemma botOrd_not_bot {b x : A} (r : A → A → Prop) (h : x ≠ b) : ¬ botOrd b r b x := by
  classical
  apply byRank_not_of_lt
  simp [h]

lemma topOrd_agree {b x y : A} (r : A → A → Prop) (hx : x ≠ b) (hy : y ≠ b) :
    topOrd b r x y ↔ r x y := by
  classical
  apply byRank_iff_of_eq
  simp [hx, hy]

lemma botOrd_agree {b x y : A} (r : A → A → Prop) (hx : x ≠ b) (hy : y ≠ b) :
    botOrd b r x y ↔ r x y := by
  classical
  apply byRank_iff_of_eq
  simp [hx, hy]

open Classical in
/-- The priority function putting `p` first, `q` second, `s` third and everything else last. -/
noncomputable def rank3 (p q s : A) : A → ℕ :=
  fun z => if z = p then 0 else if z = q then 1 else if z = s then 2 else 3

open Classical in
/-- The priority function used in the extremal lemma: `b` is kept at the top (if `top` holds)
or at the bottom, and `y` is put above everything else. -/
noncomputable def rankExtremal (b y : A) (top : Prop) : A → ℕ :=
  fun z => if z = b then (if top then 0 else 3) else if z = y then 1 else 2

lemma rankExtremal_top {b y : A} {top : Prop} (h : top) : rankExtremal b y top b = 0 := by
  classical
  simp [rankExtremal, h]

lemma rankExtremal_bot {b y : A} {top : Prop} (h : ¬ top) : rankExtremal b y top b = 3 := by
  classical
  simp [rankExtremal, h]

lemma rankExtremal_snd {b y : A} {top : Prop} (h : y ≠ b) : rankExtremal b y top y = 1 := by
  classical
  simp [rankExtremal, h]

lemma rankExtremal_rest {b y z : A} {top : Prop} (h1 : z ≠ b) (h2 : z ≠ y) :
    rankExtremal b y top z = 2 := by
  classical
  simp [rankExtremal, h1, h2]

open Classical in
/-- The priority function inserting `b` just below `x` and above everything that `x` beats. -/
noncomputable def rankMid (b x : A) (below : A → Prop) : A → ℕ :=
  fun z => if z = b then 1 else if (z = x ∨ below z) then 0 else 2

lemma rankMid_mid (b x : A) (below : A → Prop) : rankMid b x below b = 1 := by
  classical
  simp [rankMid]

lemma rankMid_fst {b x : A} {below : A → Prop} (h : x ≠ b) : rankMid b x below x = 0 := by
  classical
  simp [rankMid, h]

lemma rankMid_last {b x y : A} {below : A → Prop} (h1 : y ≠ b) (h2 : y ≠ x) (h3 : ¬ below y) :
    rankMid b x below y = 2 := by
  classical
  simp [rankMid, h1, h2, h3]

/-! ## The extremal lemma -/

/-- If an alternative `b` is ranked at the very top or at the very bottom by every voter, then
it also sits at the very top or at the very bottom of the social ranking. -/
lemma extremal (S : SWF A n) {P : Fin n → A → A → Prop} (hP : IsProfile P) (b : A)
    (hext : ∀ i, (∀ x, x ≠ b → P i b x) ∨ (∀ x, x ≠ b → P i x b)) :
    (∀ x, x ≠ b → S.F P b x) ∨ (∀ x, x ≠ b → S.F P x b) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨x, hxb, hx⟩, ⟨y, hyb, hy⟩⟩ := hcon
  have hFxb : S.F P x b := ((S.rational P hP).total x b hxb).resolve_right hx
  have hFby : S.F P b y := ((S.rational P hP).total b y (Ne.symm hyb)).resolve_right hy
  have hxy : x ≠ y := by
    rintro rfl
    exact (S.rational P hP).asymm _ _ hFxb hFby
  -- the new profile: keep `b` where it is, and move `y` above `x` for everybody
  set rk : Fin n → A → ℕ := fun i => rankExtremal b y (∀ w, w ≠ b → P i b w) with hrk
  set P' : Fin n → A → A → Prop := fun i => byRank (rk i) (P i) with hP'
  have hP'prof : IsProfile P' := fun i => isRanking_byRank _ (hP i)
  have hb0 : ∀ i, (∀ w, w ≠ b → P i b w) → rk i b = 0 := by
    intro i hi
    simp only [hrk]
    exact rankExtremal_top hi
  have hb3 : ∀ i, ¬ (∀ w, w ≠ b → P i b w) → rk i b = 3 := by
    intro i hi
    simp only [hrk]
    exact rankExtremal_bot hi
  have hy1 : ∀ i, rk i y = 1 := by
    intro i
    simp only [hrk]
    exact rankExtremal_snd hyb
  have hz2 : ∀ i, ∀ z : A, z ≠ b → z ≠ y → rk i z = 2 := by
    intro i z h1 h2
    simp only [hrk]
    exact rankExtremal_rest h1 h2
  -- everybody ranks `y` above `x`
  have hyx : ∀ i, P' i y x := by
    intro i
    apply byRank_of_lt
    rw [hy1 i, hz2 i x hxb hxy]
    omega
  have hpar : S.F P' y x := S.pareto P' hP'prof y x hyx
  -- `b` keeps its extremal position, so the pairs `(x,b)` and `(b,y)` are unchanged
  have hpair : ∀ z : A, z ≠ b → z ≠ y → ∀ i, (P i z b ↔ P' i z b) ∧ (P i b z ↔ P' i b z) := by
    intro z hzb hzy i
    by_cases htop : (∀ w, w ≠ b → P i b w)
    · have h1 : P i b z := htop z hzb
      have h2 : ¬ P i z b := (hP i).asymm _ _ h1
      have h3 : P' i b z := by
        apply byRank_of_lt
        rw [hb0 i htop, hz2 i z hzb hzy]
        omega
      have h4 : ¬ P' i z b := (hP'prof i).asymm _ _ h3
      exact ⟨by simp [h2, h4], by simp [h1, h3]⟩
    · have hbot : ∀ w, w ≠ b → P i w b := (hext i).resolve_left htop
      have h1 : P i z b := hbot z hzb
      have h2 : ¬ P i b z := (hP i).asymm _ _ h1
      have h3 : P' i z b := by
        apply byRank_of_lt
        rw [hb3 i htop, hz2 i z hzb hzy]
        omega
      have h4 : ¬ P' i b z := (hP'prof i).asymm _ _ h3
      exact ⟨by simp [h1, h3], by simp [h2, h4]⟩
  have hxb' : S.F P' x b :=
    (S.iia P P' hP hP'prof x b (fun i => hpair x hxb hxy i)).mp hFxb
  have hby' : S.F P' b y := by
    have hy' : ∀ i, (P i b y ↔ P' i b y) ∧ (P i y b ↔ P' i y b) := by
      intro i
      by_cases htop : (∀ w, w ≠ b → P i b w)
      · have h1 : P i b y := htop y hyb
        have h2 : ¬ P i y b := (hP i).asymm _ _ h1
        have h3 : P' i b y := by
          apply byRank_of_lt
          rw [hb0 i htop, hy1 i]
          omega
        have h4 : ¬ P' i y b := (hP'prof i).asymm _ _ h3
        exact ⟨by simp [h1, h3], by simp [h2, h4]⟩
      · have hbot : ∀ w, w ≠ b → P i w b := (hext i).resolve_left htop
        have h1 : P i y b := hbot y hyb
        have h2 : ¬ P i b y := (hP i).asymm _ _ h1
        have h3 : P' i y b := by
          apply byRank_of_lt
          rw [hy1 i, hb3 i htop]
          omega
        have h4 : ¬ P' i b y := (hP'prof i).asymm _ _ h3
        exact ⟨by simp [h2, h4], by simp [h1, h3]⟩
    exact (S.iia P P' hP hP'prof b y hy').mp hFby
  have hxy' : S.F P' x y := (S.rational P' hP'prof).trans' _ _ _ hxb' hby'
  exact (S.rational P' hP'prof).asymm _ _ hxy' hpar

/-! ## The pivotal voter -/

open Classical in
/-- The `k`-th stage profile for `b`: the first `k` voters put `b` on top, all the others put
`b` at the bottom. -/
noncomputable def stage (b : A) (r : A → A → Prop) (k : ℕ) : Fin n → A → A → Prop :=
  fun i => if (i : ℕ) < k then topOrd b r else botOrd b r

lemma stage_of_lt {b : A} {r : A → A → Prop} {k : ℕ} {i : Fin n} (h : (i : ℕ) < k) :
    stage b r k i = topOrd b r := by
  simp only [stage, if_pos h]

lemma stage_of_not_lt {b : A} {r : A → A → Prop} {k : ℕ} {i : Fin n} (h : ¬ (i : ℕ) < k) :
    stage b r k i = botOrd b r := by
  simp only [stage, if_neg h]

lemma isProfile_stage (b : A) {r : A → A → Prop} (hr : IsRanking r) (k : ℕ) :
    IsProfile (stage (n := n) b r k) := by
  intro i
  by_cases h : (i : ℕ) < k
  · rw [stage_of_lt h]; exact isRanking_topOrd b hr
  · rw [stage_of_not_lt h]; exact isRanking_botOrd b hr

lemma stage_extremal (b : A) (r : A → A → Prop) (k : ℕ) (i : Fin n) :
    (∀ x, x ≠ b → stage b r k i b x) ∨ (∀ x, x ≠ b → stage b r k i x b) := by
  by_cases h : (i : ℕ) < k
  · rw [stage_of_lt h]; exact Or.inl fun x hx => topOrd_top r hx
  · rw [stage_of_not_lt h]; exact Or.inr fun x hx => botOrd_bot r hx

lemma exists_step (T : ℕ → Prop) (h0 : ¬ T 0) : ∀ m : ℕ, T m → ∃ k < m, ¬ T k ∧ T (k + 1) := by
  intro m
  induction m with
  | zero => intro h; exact absurd h h0
  | succ m ih =>
    intro h
    by_cases hm : T m
    · obtain ⟨k, hk, hk1, hk2⟩ := ih hm
      exact ⟨k, by omega, hk1, hk2⟩
    · exact ⟨m, by omega, hm, h⟩

/-- There is a pivotal voter `k` for `b`: the alternative `b` is socially at the bottom at
stage `k` and socially at the top at stage `k + 1`. -/
lemma exists_pivot (S : SWF A n) {r : A → A → Prop} (hr : IsRanking r) (b x0 : A) (hx0 : x0 ≠ b) :
    ∃ k : ℕ, k < n ∧ (∀ x, x ≠ b → S.F (stage b r k) x b) ∧
      (∀ x, x ≠ b → S.F (stage b r (k + 1)) b x) := by
  classical
  set T : ℕ → Prop := fun k => ∀ x, x ≠ b → S.F (stage (n := n) b r k) b x with hT
  have hTn : T n := by
    intro x hx
    refine S.pareto _ (isProfile_stage b hr n) b x ?_
    intro i
    rw [stage_of_lt i.isLt]
    exact topOrd_top r hx
  have hT0 : ¬ T 0 := by
    intro h
    have h1 : S.F (stage (n := n) b r 0) x0 b := by
      refine S.pareto _ (isProfile_stage b hr 0) x0 b ?_
      intro i
      rw [stage_of_not_lt (by omega : ¬ (i : ℕ) < 0)]
      exact botOrd_bot r hx0
    exact (S.rational _ (isProfile_stage b hr 0)).asymm _ _ h1 (h x0 hx0)
  obtain ⟨k, hkn, hk1, hk2⟩ := exists_step T hT0 n hTn
  refine ⟨k, hkn, ?_, hk2⟩
  exact (extremal S (isProfile_stage b hr k) b (stage_extremal b r k)).resolve_left hk1

/-! ## A local dictator -/

/-- The pivotal voter for `b` dictates the social ranking of every pair of alternatives which
does not involve `b`. -/
lemma local_dictator (S : SWF A n) (b x0 : A) (hx0 : x0 ≠ b) :
    ∃ d : Fin n, ∀ Q, IsProfile Q → ∀ x y, x ≠ b → y ≠ b → Q d x y → S.F Q x y := by
  classical
  obtain ⟨r, hr⟩ := exists_ranking A
  obtain ⟨k, hkn, hbot, htop⟩ := exists_pivot S hr b x0 hx0
  obtain ⟨d, hdk⟩ : ∃ d : Fin n, (d : ℕ) = k := ⟨⟨k, hkn⟩, rfl⟩
  refine ⟨d, ?_⟩
  intro Q hQ x y hxb hyb hQxy
  have hxy : x ≠ y := (hQ d).ne' hQxy
  have hnyx : ¬ Q d y x := (hQ d).asymm _ _ hQxy
  have hdnlt : ¬ ((d : ℕ) < k) := by omega
  -- the auxiliary profile: `b` is inserted between `x` and `y` in the pivotal voter's ranking
  set rkd : A → ℕ := rankMid b x (fun z => Q d z x) with hrkd
  set P : Fin n → A → A → Prop := fun i =>
    if (i : ℕ) < k then topOrd b (Q i)
    else if (i : ℕ) = k then byRank rkd (Q i)
    else botOrd b (Q i) with hP
  have hPlt : ∀ i : Fin n, (i : ℕ) < k → P i = topOrd b (Q i) := by
    intro i h; simp only [hP, if_pos h]
  have hPgt : ∀ i : Fin n, ¬ (i : ℕ) < k → (i : ℕ) ≠ k → P i = botOrd b (Q i) := by
    intro i h1 h2; simp only [hP, if_neg h1, if_neg h2]
  have hPd : P d = byRank rkd (Q d) := by
    simp only [hP, if_neg hdnlt, if_pos hdk]
  have hPprof : IsProfile P := by
    intro i
    by_cases h1 : (i : ℕ) < k
    · rw [hPlt i h1]; exact isRanking_topOrd b (hQ i)
    · by_cases h2 : (i : ℕ) = k
      · have : i = d := Fin.ext (by omega)
        rw [this, hPd]; exact isRanking_byRank _ (hQ d)
      · rw [hPgt i h1 h2]; exact isRanking_botOrd b (hQ i)
  have hrkx : rkd x = 0 := by
    simp only [hrkd]
    exact rankMid_fst hxb
  have hrkb : rkd b = 1 := by
    simp only [hrkd]
    exact rankMid_mid b x _
  have hrky : rkd y = 2 := by
    simp only [hrkd]
    exact rankMid_last hyb (Ne.symm hxy) hnyx
  -- the pair `(x, b)` matches stage `k`
  have hxbP : S.F P x b := by
    have hmatch : ∀ i, (P i x b ↔ stage (n := n) b r k i x b) ∧
        (P i b x ↔ stage (n := n) b r k i b x) := by
      intro i
      by_cases h1 : (i : ℕ) < k
      · rw [hPlt i h1, stage_of_lt h1]
        exact ⟨by simp [topOrd_not_top (Q i) hxb, topOrd_not_top r hxb],
          by simp [topOrd_top (Q i) hxb, topOrd_top r hxb]⟩
      · by_cases h2 : (i : ℕ) = k
        · have hid : i = d := Fin.ext (by omega)
          rw [hid, hPd, stage_of_not_lt hdnlt]
          constructor
          · simp [byRank_of_lt (show rkd x < rkd b by omega), botOrd_bot r hxb]
          · simp [byRank_not_of_lt (show rkd x < rkd b by omega), botOrd_not_bot r hxb]
        · rw [hPgt i h1 h2, stage_of_not_lt h1]
          exact ⟨by simp [botOrd_bot (Q i) hxb, botOrd_bot r hxb],
            by simp [botOrd_not_bot (Q i) hxb, botOrd_not_bot r hxb]⟩
    exact (S.iia P _ hPprof (isProfile_stage b hr k) x b hmatch).mpr (hbot x hxb)
  -- the pair `(b, y)` matches stage `k + 1`
  have hbyP : S.F P b y := by
    have hmatch : ∀ i, (P i b y ↔ stage (n := n) b r (k + 1) i b y) ∧
        (P i y b ↔ stage (n := n) b r (k + 1) i y b) := by
      intro i
      by_cases h1 : (i : ℕ) < k
      · rw [hPlt i h1, stage_of_lt (by omega : (i : ℕ) < k + 1)]
        exact ⟨by simp [topOrd_top (Q i) hyb, topOrd_top r hyb],
          by simp [topOrd_not_top (Q i) hyb, topOrd_not_top r hyb]⟩
      · by_cases h2 : (i : ℕ) = k
        · have hid : i = d := Fin.ext (by omega)
          rw [hid, hPd, stage_of_lt (by omega : (d : ℕ) < k + 1)]
          constructor
          · simp [byRank_of_lt (show rkd b < rkd y by omega), topOrd_top r hyb]
          · simp [byRank_not_of_lt (show rkd b < rkd y by omega), topOrd_not_top r hyb]
        · rw [hPgt i h1 h2, stage_of_not_lt (by omega : ¬ (i : ℕ) < k + 1)]
          exact ⟨by simp [botOrd_not_bot (Q i) hyb, botOrd_not_bot r hyb],
            by simp [botOrd_bot (Q i) hyb, botOrd_bot r hyb]⟩
    exact (S.iia P _ hPprof (isProfile_stage b hr (k + 1)) b y hmatch).mpr (htop y hyb)
  have hxyP : S.F P x y := (S.rational P hPprof).trans' _ _ _ hxbP hbyP
  -- the pair `(x, y)` matches the original profile `Q`
  have hmatch : ∀ i, (P i x y ↔ Q i x y) ∧ (P i y x ↔ Q i y x) := by
    intro i
    by_cases h1 : (i : ℕ) < k
    · rw [hPlt i h1]
      exact ⟨topOrd_agree _ hxb hyb, topOrd_agree _ hyb hxb⟩
    · by_cases h2 : (i : ℕ) = k
      · have hid : i = d := Fin.ext (by omega)
        rw [hid, hPd]
        constructor
        · simp [byRank_of_lt (show rkd x < rkd y by omega), hQxy]
        · simp [byRank_not_of_lt (show rkd x < rkd y by omega), hnyx]
      · rw [hPgt i h1 h2]
        exact ⟨botOrd_agree _ hxb hyb, botOrd_agree _ hyb hxb⟩
  exact (S.iia P Q hPprof hQ x y hmatch).mp hxyP

/-! ## Uniqueness of the local dictator -/

/-- Two local dictators for different excluded alternatives coincide. -/
lemma local_dictator_unique (S : SWF A n) {u v w : Fin n} {p q s : A}
    (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s)
    (hu : ∀ Q, IsProfile Q → ∀ x y, x ≠ p → y ≠ p → Q u x y → S.F Q x y)
    (hv : ∀ Q, IsProfile Q → ∀ x y, x ≠ q → y ≠ q → Q v x y → S.F Q x y)
    (hw : ∀ Q, IsProfile Q → ∀ x y, x ≠ s → y ≠ s → Q w x y → S.F Q x y) :
    u = v := by
  classical
  by_contra huv
  obtain ⟨r, hr⟩ := exists_ranking A
  -- a Condorcet-style cyclic profile
  set Q : Fin n → A → A → Prop :=
    fun i => if i = v then byRank (rank3 q p s) r else byRank (rank3 s q p) r with hQdef
  have hQv : Q v = byRank (rank3 q p s) r := by simp only [hQdef, if_pos rfl]
  have hQother : ∀ i, i ≠ v → Q i = byRank (rank3 s q p) r := by
    intro i h; simp only [hQdef, if_neg h]
  have hQ : IsProfile Q := by
    intro i
    by_cases h : i = v
    · rw [h, hQv]; exact isRanking_byRank _ hr
    · rw [hQother i h]; exact isRanking_byRank _ hr
  have hQu : Q u s q := by
    rw [hQother u huv]
    exact byRank_of_lt (by simp [rank3, hqs])
  have hQvp : Q v p s := by
    rw [hQv]
    exact byRank_of_lt (by simp [rank3, hpq, hps.symm, hqs.symm])
  have hQw : Q w q p := by
    by_cases hwv : w = v
    · rw [hwv, hQv]
      exact byRank_of_lt (by simp [rank3, hpq])
    · rw [hQother w hwv]
      exact byRank_of_lt (by simp [rank3, hpq, hps, hqs])
  have h1 : S.F Q s q := hu Q hQ s q (Ne.symm hps) (Ne.symm hpq) hQu
  have h2 : S.F Q q p := hw Q hQ q p hqs hps hQw
  have h3 : S.F Q p s := hv Q hQ p s hpq (Ne.symm hqs) hQvp
  have h4 : S.F Q s p := (S.rational Q hQ).trans' _ _ _ h1 h2
  exact (S.rational Q hQ).asymm _ _ h4 h3

/-! ## Arrow's theorem -/

/-- **Arrow's theorem**: on at least three alternatives, every rational, unanimous social
welfare function satisfying independence of irrelevant alternatives has a dictator. -/
theorem exists_dictator (S : SWF A n) {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ d : Fin n, IsDictator S.F d := by
  classical
  obtain ⟨d, hd⟩ := local_dictator S b a hab
  -- `d` also dictates over every pair avoiding a suitable third alternative
  have key : ∀ e : A, e ≠ b → (e = a ∨ e = c) →
      ∀ Q, IsProfile Q → ∀ x y, x ≠ e → y ≠ e → Q d x y → S.F Q x y := by
    intro e heb hea Q hQ x y hxe hye hQxy
    obtain ⟨s, hbs, hes⟩ : ∃ s : A, b ≠ s ∧ e ≠ s := by
      rcases hea with rfl | rfl
      · exact ⟨c, hbc, hac⟩
      · exact ⟨a, Ne.symm hab, Ne.symm hac⟩
    obtain ⟨d', hd'⟩ := local_dictator S e b (Ne.symm heb)
    obtain ⟨d'', hd''⟩ := local_dictator S s b hbs
    have hdd' : d = d' :=
      local_dictator_unique S (u := d) (v := d') (w := d'') (Ne.symm heb) hbs hes hd hd' hd''
    exact hd' Q hQ x y hxe hye (hdd' ▸ hQxy)
  refine ⟨d, ?_⟩
  intro Q hQ x y hQxy
  by_cases hxb : x = b
  · subst hxb
    by_cases hya : y = a
    · subst hya
      exact key c (Ne.symm hbc) (Or.inr rfl) Q hQ _ _ hbc hac hQxy
    · exact key a hab (Or.inl rfl) Q hQ _ _ (Ne.symm hab) hya hQxy
  · by_cases hyb : y = b
    · subst hyb
      by_cases hxa : x = a
      · subst hxa
        exact key c (Ne.symm hbc) (Or.inr rfl) Q hQ _ _ hac hbc hQxy
      · exact key a hab (Or.inl rfl) Q hQ _ _ hxa (Ne.symm hab) hQxy
    · exact hd Q hQ x y hxb hyb hQxy

/-- **Arrow's impossibility theorem**: with at least three alternatives, no ranked voting rule
is simultaneously rational, unanimous, independent of irrelevant alternatives and
non-dictatorial. -/
theorem arrow_impossibility {A : Type*} {n : ℕ} {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (F : (Fin n → A → A → Prop) → (A → A → Prop))
    (hrat : ∀ P, IsProfile P → IsRanking (F P))
    (hpar : ∀ P, IsProfile P → ∀ x y, (∀ i, P i x y) → F P x y)
    (hiia : ∀ P Q, IsProfile P → IsProfile Q → ∀ x y,
      (∀ i, (P i x y ↔ Q i x y) ∧ (P i y x ↔ Q i y x)) → (F P x y ↔ F Q x y))
    (hnd : ∀ d : Fin n, ¬ IsDictator F d) : False := by
  obtain ⟨d, hd⟩ := exists_dictator ⟨F, hrat, hpar, hiia⟩ hab hac hbc
  exact hnd d hd

/-! ## Consistency of the remaining axioms

The dictatorship rule satisfies rationality, unanimity and independence of irrelevant
alternatives, so the hypotheses of `arrow_impossibility` other than non-dictatorship are
consistent and the impossibility theorem above is not vacuous. -/

/-- The rule which always copies voter `d`'s ranking. -/
def dictatorship (A : Type*) {n : ℕ} (d : Fin n) : SWF A n where
  F := fun P => P d
  rational := fun _ hP => hP d
  pareto := fun _ _ _ _ h => h d
  iia := fun _ _ _ _ _ _ h => (h d).1

lemma isDictator_dictatorship (A : Type*) {n : ℕ} (d : Fin n) :
    IsDictator (dictatorship A d).F d := fun _ _ _ _ h => h

end Frontier

