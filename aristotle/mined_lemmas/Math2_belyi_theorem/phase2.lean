import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/

lemma phase2 : ∀ N : ℕ, ∀ T : Finset ℚ, (∀ q ∈ T, 0 ≤ q ∧ q ≤ 1) → (0 : ℚ) ∈ T →
    (1 : ℚ) ∈ T → T.card ≤ N →
    ∃ g : ℚ[X], 0 < g.natDegree ∧ (∀ q ∈ T, g.eval q = 0 ∨ g.eval q = 1) ∧
      (∀ x : ℚ, 0 ≤ x → x ≤ 1 → 0 ≤ g.eval x ∧ g.eval x ≤ 1) ∧
      (∀ c : ℂ, aeval c (derivative g) = 0 → aeval c g = 0 ∨ aeval c g = 1) := by
  intro N
  induction N with
  | zero =>
    intro T _ h0 _ hcard
    have := Finset.card_pos.2 ⟨0, h0⟩
    omega
  | succ N IH =>
    intro T hT h0 h1 hcard
    by_cases hsmall : T.card ≤ N
    · exact IH T hT h0 h1 hsmall
    by_cases htriv : ∀ q ∈ T, q = 0 ∨ q = 1
    · refine ⟨X, by simp, fun q hq => by simpa using htriv q hq,
        fun x hx0 hx1 => by simpa using ⟨hx0, hx1⟩, fun c hc => by simp at hc⟩
    push_neg at htriv
    obtain ⟨lam, hlamT, hlam0, hlam1⟩ := htriv
    obtain ⟨hlamge, hlamle⟩ := hT lam hlamT
    have hl0 : 0 < lam := lt_of_le_of_ne hlamge (Ne.symm hlam0)
    have hl1 : lam < 1 := lt_of_le_of_ne hlamle hlam1
    obtain ⟨a, b, hab⟩ := exists_belyiCrit hl0 hl1
    set f := belyiPoly a b with hf
    set T' : Finset ℚ := T.image f.eval ∪ {0, 1} with hT'def
    have hev0 : f.eval 0 = 0 := belyiPoly_eval_zero a b
    have hev1 : f.eval 1 = 0 := belyiPoly_eval_one a b
    have hevl : f.eval lam = 1 := by rw [← hab]; exact belyiPoly_eval_crit a b
    have hT'mem : ∀ q ∈ T', 0 ≤ q ∧ q ≤ 1 := by
      intro q hq
      rw [hT'def, Finset.mem_union] at hq
      rcases hq with hq | hq
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
        exact belyiPoly_maps_unit_interval a b (hT r hr).1 (hT r hr).2
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl <;> norm_num
    have h0' : (0:ℚ) ∈ T' := Finset.mem_union_right _ (by simp)
    have h1' : (1:ℚ) ∈ T' := Finset.mem_union_right _ (by simp)
    have hcard' : T'.card ≤ N := by
      have hsub : T' ⊆ (T \ {0, 1, lam}).image f.eval ∪ {0, 1} := by
        intro q hq
        rw [hT'def, Finset.mem_union] at hq
        rcases hq with hq | hq
        · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
          by_cases hmem : r = 0 ∨ r = 1 ∨ r = lam
          · refine Finset.mem_union_right _ ?_
            rcases hmem with rfl | rfl | rfl
            · simp [hev0]
            · simp [hev1]
            · simp [hevl]
          · push_neg at hmem
            refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨r, ?_, rfl⟩)
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            exact ⟨hr, by tauto⟩
        · exact Finset.mem_union_right _ hq
      have hss : ({0, 1, lam} : Finset ℚ) ⊆ T := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact hlamT
      have h3 : ({0, 1, lam} : Finset ℚ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hlam0]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hlam1])]
        simp
      have hsd : (T \ ({0, 1, lam} : Finset ℚ)).card = T.card - 3 := by
        rw [Finset.card_sdiff_of_subset hss, h3]
      have hu := Finset.card_union_le ((T \ ({0, 1, lam} : Finset ℚ)).image f.eval)
        ({0, 1} : Finset ℚ)
      have himg := Finset.card_image_le (s := T \ ({0, 1, lam} : Finset ℚ)) (f := f.eval)
      have h2 : ({0, 1} : Finset ℚ).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      have hmain := Finset.card_le_card hsub
      have hTcard : 3 ≤ T.card := h3 ▸ Finset.card_le_card hss
      omega
    obtain ⟨g, hg1, hg2, hg3, hg4⟩ := IH T' hT'mem h0' h1' hcard'
    have e0 : aeval (0:ℂ) g = algebraMap ℚ ℂ (g.eval 0) := by
      simpa using aeval_ratPoint (0:ℚ) g
    have e1 : aeval (1:ℂ) g = algebraMap ℚ ℂ (g.eval 1) := by
      simpa using aeval_ratPoint (1:ℚ) g
    have hval01 : ∀ q : ℚ, q ∈ T' → algebraMap ℚ ℂ (g.eval q) = 0 ∨
        algebraMap ℚ ℂ (g.eval q) = 1 := by
      intro q hq
      rcases hg2 q hq with he | he
      · exact Or.inl (by rw [he, map_zero])
      · exact Or.inr (by rw [he, map_one])
    refine ⟨g.comp f, ?_, ?_, ?_, ?_⟩
    · rw [natDegree_comp]
      have hfd : 0 < f.natDegree := by rw [hf, belyiPoly_natDegree]; omega
      exact Nat.mul_pos hg1 hfd
    · intro q hq
      rw [eval_comp]
      exact hg2 _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨q, hq, rfl⟩))
    · intro x hx0 hx1
      rw [eval_comp]
      obtain ⟨hb0, hb1⟩ := belyiPoly_maps_unit_interval a b hx0 hx1
      exact hg3 _ hb0 hb1
    · intro c hc
      rw [aeval_comp]
      rcases critval_comp hc with h | h
      · rcases belyiPoly_critval a b h with hv | hv
        · rw [hv, e0]
          exact hval01 0 h0'
        · rw [hv, e1]
          exact hval01 1 h1'
      · exact hg4 _ h


/-! ### Belyi's theorem for the projective line -/

/-- **Belyi's theorem** (for `ℙ¹`): for every finite set `S` of algebraic numbers there is a
nonconstant map `f : ℙ¹ → ℙ¹` defined over `ℚ` (here a polynomial, so that `∞ ↦ ∞`) which
sends `S` into `{0, 1}` and all of whose finite critical values lie in `{0, 1}`; that is,
`f` is ramified only over `{0, 1, ∞}`. -/
