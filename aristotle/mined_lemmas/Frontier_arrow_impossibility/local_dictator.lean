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
