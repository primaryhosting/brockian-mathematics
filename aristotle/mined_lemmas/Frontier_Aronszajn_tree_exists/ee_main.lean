import Mathlib
-- (Lean 4 requires `import` commands to precede any module docstring, so the required
-- header comment is reproduced verbatim immediately below.)

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Set Cardinal
open scoped Ordinal

namespace Aronszajn

/-! ## Countable ordinals -/

/-- An ordinal is countable (i.e. its set of predecessors is countable) iff it is `< ω₁`. -/

lemma ee_main : ∀ α : Ordinal.{0}, α < ω₁ →
    (∀ n : ℕ, {ξ : Ordinal.{0} | ξ < α ∧ ee α ξ = n}.Finite) ∧
      (∀ β < α, {ξ : Ordinal.{0} | ξ < β ∧ ee α ξ ≠ ee β ξ}.Finite) := by
  intro α
  induction α using Ordinal.induction with
  | _ α IH =>
    intro hα
    have IHfib : ∀ γ < α, ∀ n : ℕ, {ξ : Ordinal.{0} | ξ < γ ∧ ee γ ξ = n}.Finite :=
      fun γ hγ => (IH γ hγ (hγ.trans hα)).1
    have IHcoh : ∀ γ < α, ∀ δ < γ, {ξ : Ordinal.{0} | ξ < δ ∧ ee γ ξ ≠ ee δ ξ}.Finite :=
      fun γ hγ => (IH γ hγ (hγ.trans hα)).2
    constructor
    · -- finite fibers
      intro n
      set F : ℕ → Set Ordinal.{0} := fun k =>
        if cs α k < α then insert (cs α k) {ξ : Ordinal.{0} | ξ < cs α k ∧ ee (cs α k) ξ ≤ n}
        else ∅ with hFdef
      have hFfin : ∀ k, (F k).Finite := by
        intro k
        by_cases h : cs α k < α
        · simp only [hFdef, if_pos h]
          exact Set.Finite.insert _ (le_finite_of_fibers (IHfib (cs α k) h) n)
        · simp only [hFdef, if_neg h]
          exact Set.finite_empty
      refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iic n) fun k _ => hFfin k) ?_
      rintro ξ ⟨hξα, hval⟩
      have hg : ∃ m, Good α ξ m := cs_spec hα hξα
      have hk := kk_spec hg
      have hmax : max (ee (cs α (kk α ξ)) ξ) (kk α ξ) = n := (ee_of_good hg).symm.trans hval
      have hkn : kk α ξ ≤ n := by omega
      have hwn : ee (cs α (kk α ξ)) ξ ≤ n := by omega
      refine Set.mem_biUnion (Set.mem_Iic.2 hkn) ?_
      simp only [hFdef, if_pos hk.2]
      rcases eq_or_lt_of_le hk.1 with h | h
      · exact Set.mem_insert_iff.2 (Or.inl h)
      · exact Set.mem_insert_of_mem _ ⟨h, hwn⟩
    · -- coherence
      intro β hβ
      obtain ⟨m, hm⟩ := cs_spec hα hβ
      set F : ℕ → Set Ordinal.{0} := fun k =>
        if cs α k < α then
          insert (cs α k)
            ({ξ : Ordinal.{0} | ξ < β ∧ ξ < cs α k ∧ ee (cs α k) ξ ≠ ee β ξ} ∪
              {ξ : Ordinal.{0} | ξ < cs α k ∧ ee (cs α k) ξ ≤ k})
        else ∅ with hFdef
      have hFfin : ∀ k, (F k).Finite := by
        intro k
        by_cases h : cs α k < α
        · simp only [hFdef, if_pos h]
          refine Set.Finite.insert _ (Set.Finite.union ?_
            (le_finite_of_fibers (IHfib (cs α k) h) k))
          rcases lt_trichotomy (cs α k) β with hlt | heq | hgt
          · refine Set.Finite.subset (IHcoh β hβ (cs α k) hlt) ?_
            rintro ξ ⟨_, h2, h3⟩
            exact ⟨h2, fun hcon => h3 hcon.symm⟩
          · refine Set.Finite.subset (Set.finite_empty) ?_
            rintro ξ ⟨_, _, h3⟩
            exact absurd (by rw [heq]) h3
          · refine Set.Finite.subset (IHcoh (cs α k) h β hgt) ?_
            rintro ξ ⟨h1, _, h3⟩
            exact ⟨h1, h3⟩
        · simp only [hFdef, if_neg h]
          exact Set.finite_empty
      refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iic m) fun k _ => hFfin k) ?_
      rintro ξ ⟨hξβ, hne⟩
      have hξα : ξ < α := hξβ.trans hβ
      have hg : ∃ j, Good α ξ j := cs_spec hα hξα
      have hk := kk_spec hg
      have hkm : kk α ξ ≤ m := kk_le ⟨hξβ.le.trans hm.1, hm.2⟩
      have hee := ee_of_good hg
      refine Set.mem_biUnion (Set.mem_Iic.2 hkm) ?_
      simp only [hFdef, if_pos hk.2]
      rcases eq_or_lt_of_le hk.1 with h | h
      · exact Set.mem_insert_iff.2 (Or.inl h)
      · refine Set.mem_insert_of_mem _ ?_
        by_cases hle : ee (cs α (kk α ξ)) ξ ≤ kk α ξ
        · exact Or.inr ⟨h, hle⟩
        · refine Or.inl ⟨hξβ, h, ?_⟩
          rw [hee] at hne
          rwa [max_eq_left (not_le.1 hle).le] at hne

