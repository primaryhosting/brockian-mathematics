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

lemma card_le_two_pow_cost (p : Proto n) (A : Finset (Fin n → Bool))
    (h : ∀ a ∈ A, ∀ b ∈ A, run p a (negVec b) = Disj a (negVec b)) :
    A.card ≤ 2 ^ cost p := by
  induction p generalizing A with
  | leaf v =>
      refine le_trans (Finset.card_le_one.mpr ?_) (by simp [cost])
      intro a ha b hb
      by_contra hne
      have hv : v = true := by
        have := h a ha a ha
        rw [run, Disj_negVec_self] at this
        exact this
      obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
        by_contra hc
        push_neg at hc
        exact hne (funext hc)
      rcases hA : a i with _ | _ <;> rcases hB : b i with _ | _
      · exact hi (by rw [hA, hB])
      · have := h b hb a ha
        rw [run, Disj_eq_false_of_mem hB hA] at this
        rw [hv] at this
        exact Bool.noConfusion this
      · have := h a ha b hb
        rw [run, Disj_eq_false_of_mem hA hB] at this
        rw [hv] at this
        exact Bool.noConfusion this
      · exact hi (by rw [hA, hB])
  | alice g f ih =>
      classical
      have hsplit : (A.filter (fun a => g a = true)).card
          + (A.filter (fun a => ¬ (g a = true))).card = A.card :=
        Finset.card_filter_add_card_filter_not _
      have h1 : (A.filter (fun a => g a = true)).card ≤ 2 ^ cost (f true) := by
        refine ih true _ (fun a ha b hb => ?_)
        rw [Finset.mem_filter] at ha
        have := h a ha.1 b (Finset.mem_filter.mp hb).1
        rwa [run, ha.2] at this
      have h0 : (A.filter (fun a => ¬ (g a = true))).card ≤ 2 ^ cost (f false) := by
        refine ih false _ (fun a ha b hb => ?_)
        rw [Finset.mem_filter] at ha
        have hga : g a = false := by simpa using ha.2
        have := h a ha.1 b (Finset.mem_filter.mp hb).1
        rwa [run, hga] at this
      have hm0 : (2:ℕ) ^ cost (f false) ≤ 2 ^ max (cost (f false)) (cost (f true)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hm1 : (2:ℕ) ^ cost (f true) ≤ 2 ^ max (cost (f false)) (cost (f true)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : A.card ≤ 2 ^ max (cost (f false)) (cost (f true))
          + 2 ^ max (cost (f false)) (cost (f true)) := by omega
      rw [cost, pow_add, pow_one]
      omega
  | bob g f ih =>
      classical
      have hsplit : (A.filter (fun b => g (negVec b) = true)).card
          + (A.filter (fun b => ¬ (g (negVec b) = true))).card = A.card :=
        Finset.card_filter_add_card_filter_not _
      have h1 : (A.filter (fun b => g (negVec b) = true)).card ≤ 2 ^ cost (f true) := by
        refine ih true _ (fun a ha b hb => ?_)
        rw [Finset.mem_filter] at hb
        have := h a (Finset.mem_filter.mp ha).1 b hb.1
        rwa [run, hb.2] at this
      have h0 : (A.filter (fun b => ¬ (g (negVec b) = true))).card ≤ 2 ^ cost (f false) := by
        refine ih false _ (fun a ha b hb => ?_)
        rw [Finset.mem_filter] at hb
        have hgb : g (negVec b) = false := by simpa using hb.2
        have := h a (Finset.mem_filter.mp ha).1 b hb.1
        rwa [run, hgb] at this
      have hm0 : (2:ℕ) ^ cost (f false) ≤ 2 ^ max (cost (f false)) (cost (f true)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hm1 : (2:ℕ) ^ cost (f true) ≤ 2 ^ max (cost (f false)) (cost (f true)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : A.card ≤ 2 ^ max (cost (f false)) (cost (f true))
          + 2 ^ max (cost (f false)) (cost (f true)) := by omega
      rw [cost, pow_add, pow_one]
      omega

end Proto

/-- **Deterministic two-way lower bound.** Any deterministic communication protocol that
computes set disjointness on an `n`-element universe must communicate at least `n` bits. -/
