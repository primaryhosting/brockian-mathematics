/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree sorting three elements.
An internal node compares the (unknown) input values at two positions `i j : Fin 3`,
and branches on the outcome; a leaf outputs a permutation. -/
inductive CompTree : Type
  | leaf : Equiv.Perm (Fin 3) → CompTree
  | node : Fin 3 → Fin 3 → CompTree → CompTree → CompTree
  deriving Inhabited

namespace CompTree

/-- The worst-case number of comparisons performed by the tree. -/

theorem card_le_two_pow_depth (t : CompTree) (S : Finset (Equiv.Perm (Fin 3)))
    (hS : ∀ σ ∈ S, t.run σ = σ) : S.card ≤ 2 ^ t.depth := by
  induction t generalizing S with
  | leaf p =>
      have : S ⊆ {p} := by
        intro σ hσ
        have := hS σ hσ
        simp [run] at this
        simp [← this]
      calc S.card ≤ ({p} : Finset (Equiv.Perm (Fin 3))).card := Finset.card_le_card this
        _ = 1 := by simp
        _ = 2 ^ (leaf p).depth := by simp [depth]
  | node i j l r ihl ihr =>
      classical
      set P : Equiv.Perm (Fin 3) → Prop := fun σ => σ i < σ j with hP
      have hsplit : (S.filter P).card + (S.filter (fun σ => ¬ P σ)).card = S.card :=
        Finset.card_filter_add_card_filter_not (p := P)
      have hl : (S.filter P).card ≤ 2 ^ l.depth := by
        refine ihl _ ?_
        intro σ hσ
        rw [Finset.mem_filter] at hσ
        have h1 := hS σ hσ.1
        rw [run, if_pos hσ.2] at h1
        exact h1
      have hr : (S.filter (fun σ => ¬ P σ)).card ≤ 2 ^ r.depth := by
        refine ihr _ ?_
        intro σ hσ
        rw [Finset.mem_filter] at hσ
        have h1 := hS σ hσ.1
        rw [run, if_neg hσ.2] at h1
        exact h1
      have hml : (2:ℕ) ^ l.depth ≤ 2 ^ max l.depth r.depth :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hmr : (2:ℕ) ^ r.depth ≤ 2 ^ max l.depth r.depth :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have key : (2:ℕ) ^ (1 + max l.depth r.depth)
          = 2 ^ max l.depth r.depth + 2 ^ max l.depth r.depth := by
        rw [pow_add]; ring
      simp only [depth]
      rw [key]
      omega

end CompTree

/-- `⌈log₂ 3!⌉ = 3`. -/
