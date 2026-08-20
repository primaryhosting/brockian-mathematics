/-
# Huffman Optimal
Category: Computer Science
Target: CS.huffman_optimal
Statement: Huffman coding minimizes expected codeword length among prefix codes.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace CS

open List

variable {α : Type*} {ι : Type*}

/-! ## Extracting a minimum-weight element from a list -/

/-- `popMin f a l` returns a pair whose first component is an element of `a :: l`
minimizing `f`, and whose second component is the remaining list. -/

lemma ks_le_one : ∀ (n : ℕ) (L : List (List Bool)), (∀ c ∈ L, c.length ≤ n) →
    PrefixFreeList L → ks L ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro L hlen hpf
      rcases L with _ | ⟨c, R⟩
      · simp [ks]
      · have : c = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (hlen c (by simp)))
        rw [prefixFreeList_eq_singleton hpf (this ▸ (by simp : c ∈ c :: R))]
        norm_num [ks]
  | succ n ih =>
      intro L hlen hpf
      by_cases hnil : [] ∈ L
      · rw [prefixFreeList_eq_singleton hpf hnil]; norm_num [ks]
      · have hne : ∀ c ∈ L, c ≠ [] := by
          intro c hc h; exact hnil (h ▸ hc)
        have half : ∀ (M : List (List Bool)) (b : Bool), (∀ c ∈ M, c ∈ L) →
            (∀ c ∈ M, c.headI = b) → PrefixFreeList M → ks M ≤ 2⁻¹ := by
          intro M b hML hb hpfM
          have hneM : ∀ c ∈ M, c ≠ [] := fun c hc => hne c (hML c hc)
          rw [ks_tail M hneM]
          have hlen' : ∀ d ∈ M.map List.tail, d.length ≤ n := by
            intro d hd
            obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
            have := hlen c (hML c hc)
            have hc0 : c.length = c.tail.length + 1 := by
              cases c with
              | nil => exact absurd rfl (hneM _ hc)
              | cons a t => simp
            omega
          have := ih (M.map List.tail) hlen' (prefixFreeList_tail b M hb hneM hpfM)
          nlinarith [ks_nonneg (M.map List.tail)]
        have hsplit : ks (L.filter (fun c => c.headI)) +
            ks (L.filter (fun c => !(c.headI))) = ks L := by
          have hp := List.filter_append_perm (fun c : List Bool => c.headI) L
          have := (hp.map (fun c : List Bool => (2:ℝ)⁻¹ ^ c.length)).sum_eq
          simpa [ks, List.map_append, List.sum_append] using this
        have h1 : ks (L.filter (fun c => c.headI)) ≤ 2⁻¹ := by
          refine half _ true (fun c hc => (List.mem_filter.1 hc).1) ?_
            (List.Pairwise.sublist (List.filter_sublist) hpf)
          intro c hc; simpa using (List.mem_filter.1 hc).2
        have h2 : ks (L.filter (fun c => !(c.headI))) ≤ 2⁻¹ := by
          refine half _ false (fun c hc => (List.mem_filter.1 hc).1) ?_
            (List.Pairwise.sublist (List.filter_sublist) hpf)
          intro c hc
          have := (List.mem_filter.1 hc).2
          simpa using this
        linarith

/-! ## Basic properties of the Kraft sum and the cost -/

