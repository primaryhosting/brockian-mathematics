/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## What is formalised here

Belyi's theorem says that a smooth projective curve is defined over `ℚ̄` if and only if it admits
a map to `ℙ¹` ramified only over `{0, 1, ∞}`.  The substantial half of Belyi's proof is the
*Belyi reduction*: an explicit algorithm which, starting from a map whose branch locus is a finite
set of algebraic points, composes it with suitable polynomials until the branch locus is contained
in `{0, 1, ∞}`.

This file formalises that algorithm over `ℚ`, in the self-contained form of an equivalence
(the statement `Math2.belyi_theorem`):

> a set `S ⊆ ℚ` is finite **iff** there is a non-constant `P ∈ ℚ[X]` which maps `S` into `{0,1}`
> and all of whose finite critical values lie in `{0,1}`.

Viewed as a self-map of `ℙ¹`, such a `P` is unramified outside `{0, 1, ∞}` (a polynomial is
totally ramified over `∞`), i.e. it *is* a Belyi map for `ℙ¹` which moreover kills the prescribed
set `S` of marked points.  The forward direction is the Belyi reduction algorithm (normalise `S`
by an affine map, then repeatedly compose with the Belyi polynomials
`c · x^m (1-x)^n`, each step lowering the number of bad values); the backward direction says that
only finitely many points can be marked this way, since `P⁻¹{0,1}` is finite.
-/

open Polynomial

namespace Math2

/-- A polynomial `P ∈ ℚ[X]` is a *Belyi polynomial* if it is non-constant and all of its finite
critical values lie in `{0, 1}`.  Viewed as a map `ℙ¹ → ℙ¹`, such a `P` is unramified outside
`{0, 1, ∞}`, the point `∞` being totally ramified for every polynomial. -/

lemma exists_isBelyiPoly (S : Finset ℚ) :
    ∃ P : ℚ[X], IsBelyiPoly P ∧ ∀ s ∈ S, P.eval s = 0 ∨ P.eval s = 1 := by
  classical
  generalize hk : S.card = k
  induction k using Nat.strong_induction_on generalizing S with
  | _ k IH =>
    subst hk
    by_cases hcard : S.card ≤ 1
    · rcases S.eq_empty_or_nonempty with rfl | hne
      · exact ⟨X, ⟨by simp, by intro x hx; simp at hx⟩, by simp⟩
      · obtain ⟨a, ha⟩ := hne
        refine ⟨X - C a, ⟨by simp, ?_⟩, ?_⟩
        · intro x hx; simp at hx
        · intro s hs
          have : s = a := Finset.card_le_one.mp hcard s hs a ha
          subst this
          left; simp
    · push_neg at hcard
      have h2 : 2 ≤ S.card := hcard
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      set a := S.min' hne with hadef
      set b := S.max' hne with hbdef
      have hab : a < b := S.min'_lt_max'_of_card (by omega)
      have hba : (0 : ℚ) < b - a := by linarith
      set A : ℚ[X] := affinePoly (1 / (b - a)) (-a / (b - a)) with hAdef
      have hAeval : ∀ x : ℚ, A.eval x = (x - a) / (b - a) := by
        intro x
        rw [hAdef, eval_affinePoly]
        field_simp
        ring
      have hA : IsBelyiPoly A := isBelyiPoly_affinePoly (by positivity) _
      set T : Finset ℚ := S.image (fun s => A.eval s) with hTdef
      have hTbounds : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 1 := by
        intro t ht
        rw [hTdef, Finset.mem_image] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        have h1 : a ≤ s := S.min'_le s hs
        have h2 : s ≤ b := S.le_max' s hs
        rw [hAeval]
        constructor
        · exact div_nonneg (by linarith) hba.le
        · rw [div_le_one hba]; linarith
      have h0T : (0 : ℚ) ∈ T := by
        rw [hTdef, Finset.mem_image]
        exact ⟨a, S.min'_mem hne, by rw [hAeval]; simp⟩
      have h1T : (1 : ℚ) ∈ T := by
        rw [hTdef, Finset.mem_image]
        refine ⟨b, S.max'_mem hne, ?_⟩
        rw [hAeval]
        field_simp
      have hcardT : T.card = S.card := by
        rw [hTdef]
        refine Finset.card_image_of_injective _ ?_
        intro x y hxy
        have hxy' : (x - a) / (b - a) = (y - a) / (b - a) := by
          rw [← hAeval, ← hAeval]; exact hxy
        have hne' : b - a ≠ 0 := ne_of_gt hba
        field_simp at hxy'
        linarith
      by_cases hT2 : T.card ≤ 2
      · -- `T = {0,1}` : the affine map already works
        have hsub : ({0, 1} : Finset ℚ) ⊆ T := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact h0T
          · exact h1T
        have hTeq : T = ({0, 1} : Finset ℚ) :=
          (Finset.eq_of_subset_of_card_le hsub (by simpa using hT2)).symm
        refine ⟨A, hA, ?_⟩
        intro s hs
        have : A.eval s ∈ T := by rw [hTdef]; exact Finset.mem_image_of_mem _ hs
        rw [hTeq] at this
        simpa using this
      · push_neg at hT2
        -- there is a third value `l`, strictly between `0` and `1`
        obtain ⟨l, hlT, hl0, hl1⟩ : ∃ l ∈ T, l ≠ 0 ∧ l ≠ 1 := by
          by_contra hcon
          push_neg at hcon
          have : T ⊆ ({0, 1} : Finset ℚ) := by
            intro x hx
            rcases eq_or_ne x 0 with rfl | hx0
            · simp
            · have := hcon x hx hx0
              simp [this]
          have hle := Finset.card_le_card this
          have hc2 : ({0, 1} : Finset ℚ).card ≤ 2 := by
            simp
          omega
        obtain ⟨hl0', hl1'⟩ := hTbounds l hlT
        have hlpos : 0 < l := lt_of_le_of_ne hl0' (Ne.symm hl0)
        have hllt : l < 1 := lt_of_le_of_ne hl1' hl1
        obtain ⟨m, n, hmn⟩ := exists_repr_of_mem_Ioo hlpos hllt
        set B : ℚ[X] := belyiPoly m n with hBdef
        have hB : IsBelyiPoly B := isBelyiPoly_belyiPoly m n
        set T' : Finset ℚ := T.image (fun t => B.eval t) with hT'def
        have hB0 : B.eval 0 = 0 := eval_belyiPoly_zero m n
        have hB1 : B.eval 1 = 0 := eval_belyiPoly_one m n
        have hBl : B.eval l = 1 := by rw [hmn]; exact eval_belyiPoly_crit m n
        -- the image is strictly smaller since `0` and `1` are identified
        have hcardT' : T'.card < T.card := by
          have hsub : T' ⊆ (T.erase 1).image (fun t => B.eval t) := by
            intro y hy
            rw [hT'def, Finset.mem_image] at hy
            obtain ⟨t, ht, rfl⟩ := hy
            rcases eq_or_ne t 1 with rfl | ht1
            · refine Finset.mem_image.mpr ⟨0, ?_, ?_⟩
              · exact Finset.mem_erase.mpr ⟨zero_ne_one, h0T⟩
              · rw [hB0, hB1]
            · exact Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨ht1, ht⟩)
          have h1 : T'.card ≤ (T.erase 1).card :=
            le_trans (Finset.card_le_card hsub) (Finset.card_image_le)
          have h2 : (T.erase 1).card = T.card - 1 := Finset.card_erase_of_mem h1T
          have : 0 < T.card := Finset.card_pos.mpr ⟨1, h1T⟩
          omega
        have h0T' : (0 : ℚ) ∈ T' := by
          rw [hT'def, Finset.mem_image]
          exact ⟨0, h0T, hB0⟩
        have h1T' : (1 : ℚ) ∈ T' := by
          rw [hT'def, Finset.mem_image]
          exact ⟨l, hlT, hBl⟩
        obtain ⟨Q, hQ, hQval⟩ := IH T'.card (by omega) T' rfl
        refine ⟨Q.comp (B.comp A), ?_, ?_⟩
        · refine isBelyiPoly_comp hQ (isBelyiPoly_comp hB hA ?_ ?_) (hQval 0 h0T') (hQval 1 h1T')
          · left; exact hB0
          · left; exact hB1
        · intro s hs
          have hAs : A.eval s ∈ T := by rw [hTdef]; exact Finset.mem_image_of_mem _ hs
          have hBs : B.eval (A.eval s) ∈ T' := by
            rw [hT'def]; exact Finset.mem_image_of_mem _ hAs
          simpa [eval_comp] using hQval _ hBs

/-! ### The main theorem -/

/-- **Belyi's theorem (rational branch points, `ℙ¹` case).**

A set `S ⊆ ℚ` of marked points is finite — i.e. is cut out by algebraic data over `ℚ` — if and
only if there is a Belyi map for `ℙ¹` killing it: a non-constant polynomial `P ∈ ℚ[X]` sending
every point of `S` into `{0, 1}` and having all of its finite critical values in `{0, 1}`.  Such a
`P`, viewed as a self-map of `ℙ¹`, is ramified only over `{0, 1, ∞}`.

The forward implication is Belyi's reduction algorithm (`Math2.exists_isBelyiPoly`); the reverse
implication holds because the fibre `P⁻¹{0,1}` of a non-constant polynomial is finite. -/
