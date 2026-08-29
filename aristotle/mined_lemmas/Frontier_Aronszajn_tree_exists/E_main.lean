/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal Set

namespace Aronszajn

/-! ## Cofinal `ω`-sequences in countable limit ordinals -/

/-- `c` is a nondecreasing `ω`-indexed sequence, starting at `0`, cofinal in `l`. -/

theorem E_main : ∀ o : Ordinal, o < ω₁ → Fto o ∧ Coh o := by
  intro o
  induction o using Ordinal.limitRecOn with
  | zero =>
    intro _
    constructor
    · intro n
      apply Set.Finite.subset (Set.finite_empty)
      rintro ξ ⟨h, -⟩
      exact absurd h (by simp)
    · intro β hβ
      exact absurd hβ (by simp)
  | succ γ ih =>
    rw [Order.succ_eq_add_one]
    intro hlt
    have hγ : γ < ω₁ := lt_trans (lt_add_one γ) hlt
    obtain ⟨ihF, ihC⟩ := ih hγ
    constructor
    · intro n
      apply Set.Finite.subset (((ihF n).union (Set.finite_singleton γ)))
      rintro ξ ⟨h1, h2⟩
      rcases lt_or_eq_of_le (Order.le_of_lt_succ h1) with h | h
      · left
        rw [E_succ, if_pos h] at h2
        exact ⟨h, h2⟩
      · right; exact h
    · intro β hβ
      rcases lt_or_eq_of_le (Order.le_of_lt_succ hβ) with h | h
      · apply Set.Finite.subset (ihC β h)
        rintro ξ ⟨h1, h2⟩
        rw [E_succ, if_pos (lt_trans h1 h)] at h2
        exact ⟨h1, h2⟩
      · apply Set.Finite.subset (Set.finite_empty)
        rintro ξ ⟨h1, h2⟩
        subst h
        rw [E_succ, if_pos h1] at h2
        exact absurd rfl h2
  | limit l hl ih =>
    intro hcl
    have hclt : ∀ k : ℕ, cseq l k < l := fun k => cseq_lt hl k
    have ihk : ∀ k : ℕ, Fto (cseq l k) ∧ Coh (cseq l k) := fun k =>
      ih _ (hclt k) (lt_trans (hclt k) hcl)
    constructor
    · intro n
      apply Set.Finite.subset
        (s := ⋃ i ∈ Set.Iic n, ⋃ m ∈ Set.Iic n,
          {ξ : Ordinal | ξ < cseq l (i + 1) ∧ E (cseq l (i + 1)) ξ = m})
        ((Set.finite_Iic n).biUnion fun i _ =>
          (Set.finite_Iic n).biUnion fun m _ => (ihk (i + 1)).1 m)
      rintro ξ ⟨h1, h2⟩
      rw [E_limit hl, if_pos h1] at h2
      have hi : idx l ξ ≤ n := h2 ▸ le_max_right _ _
      have hm : E (cseq l (idx l ξ + 1)) ξ ≤ n := h2 ▸ le_max_left _ _
      simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_setOf_eq, exists_prop]
      exact ⟨idx l ξ, hi, E (cseq l (idx l ξ + 1)) ξ, hm, idx_spec hl hcl h1, rfl⟩
    · intro β hβ
      obtain ⟨N, hN⟩ := (cseq_spec hl hcl).2.2.2 β hβ
      have hmono : Monotone (cseq l) := (cseq_spec hl hcl).2.1
      have hBig : {ξ : Ordinal | ξ < cseq l N ∧ E l ξ ≠ E (cseq l N) ξ}.Finite := by
        apply Set.Finite.subset
          (s := ⋃ k ∈ Set.Iio N,
            ({ξ : Ordinal | ξ < cseq l (k + 1) ∧ E (cseq l (k + 1)) ξ ≠ E (cseq l N) ξ} ∪
              ⋃ m ∈ Set.Iio k, {ξ : Ordinal | ξ < cseq l (k + 1) ∧ E (cseq l (k + 1)) ξ = m}))
          ((Set.finite_Iio N).biUnion fun k hk => Set.Finite.union ?_
            ((Set.finite_Iio k).biUnion fun m _ => (ihk (k + 1)).1 m))
        · rintro ξ ⟨h1, h2⟩
          have hξl : ξ < l := lt_trans h1 (hclt N)
          have hiN : idx l ξ < N := idx_lt_of_lt_cseq hl hcl h1
          have hξi : ξ < cseq l (idx l ξ + 1) := idx_spec hl hcl hξl
          rw [E_limit hl, if_pos hξl] at h2
          simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_union, Set.mem_setOf_eq, exists_prop]
          refine ⟨idx l ξ, hiN, ?_⟩
          rcases le_or_gt (idx l ξ) (E (cseq l (idx l ξ + 1)) ξ) with h | h
          · left
            refine ⟨hξi, ?_⟩
            rwa [max_eq_left h] at h2
          · right
            exact ⟨E (cseq l (idx l ξ + 1)) ξ, h, hξi, rfl⟩
        · have hle : cseq l (k + 1) ≤ cseq l N := hmono (by simpa using hk)
          rcases lt_or_eq_of_le hle with h | h
          · exact ((ihk N).2 _ h).subset (by rintro ξ ⟨h1, h2⟩; exact ⟨h1, Ne.symm h2⟩)
          · apply Set.Finite.subset Set.finite_empty
            rintro ξ ⟨-, h2⟩
            rw [h] at h2
            exact absurd rfl h2
      have h2 : {ξ : Ordinal | ξ < β ∧ E (cseq l N) ξ ≠ E β ξ}.Finite := (ihk N).2 β hN
      apply Set.Finite.subset (hBig.union h2)
      rintro ξ ⟨h1, hne⟩
      rcases eq_or_ne (E l ξ) (E (cseq l N) ξ) with h | h
      · right; exact ⟨h1, by rw [← h]; exact hne⟩
      · left; exact ⟨lt_trans h1 hN, h⟩

/-! ## Facts about `ω₁` -/

