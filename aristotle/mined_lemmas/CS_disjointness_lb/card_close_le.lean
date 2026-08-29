import Mathlib
import RequestProject.DisjointnessLb

/-!
# Deterministic two-way communication complexity of set disjointness

As a companion to `CS.disjointness_lb` (a linear lower bound for *randomized* one-way
protocols), this file formalises the general *two-way deterministic* model as protocol
trees and proves the classical fooling-set lower bound: any deterministic protocol
computing set disjointness on an `n`-element universe has cost at least `n`.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- Bitwise complement of a characteristic vector. -/

private lemma card_close_le (n c : ℕ) (m : (Fin n → Bool) → Fin (2 ^ c))
    (y : Fin (2 ^ c) → (Fin n → Bool)) :
    ((Finset.univ.filter (fun a : Fin n → Bool =>
        8 * (Finset.univ.filter (fun i => y (m a) i ≠ a i)).card ≤ n)).card)
      ≤ 2 ^ c * ∑ j ∈ range (n / 8 + 1), n.choose j := by
  classical
  set k := n / 8 with hk
  set T : Finset (Fin (2 ^ c) × Finset (Fin n)) :=
    (univ : Finset (Fin (2 ^ c))) ×ˢ
      ((range (k + 1)).biUnion (fun j => Finset.powersetCard j (univ : Finset (Fin n)))) with hT
  have hTcard : T.card ≤ 2 ^ c * ∑ j ∈ range (k + 1), n.choose j := by
    rw [hT, Finset.card_product]
    simp only [Finset.card_univ, Fintype.card_fin]
    refine Nat.mul_le_mul_left _ (le_trans Finset.card_biUnion_le ?_)
    simp [Finset.card_powersetCard]
  refine le_trans (Finset.card_le_card_of_injOn
    (fun a => (m a, Finset.univ.filter (fun i => y (m a) i ≠ a i))) ?_ ?_) hTcard
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha
    simp only [hT, Finset.mem_coe, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_range]
    refine ⟨(Finset.univ.filter (fun i => y (m a) i ≠ a i)).card, by omega, ?_⟩
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, rfl⟩
  · intro a ha b hb hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    funext i
    have hi := congrArg (fun S => i ∈ S) h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at hi
    rw [h1] at hi
    revert hi
    cases y (m b) i <;> cases hA : a i <;> cases hB : b i <;> simp

/-- Markov step: if the average error count is at most `2^n * n / 16`, then fewer than
half of the inputs have error count larger than `n / 8`. -/
