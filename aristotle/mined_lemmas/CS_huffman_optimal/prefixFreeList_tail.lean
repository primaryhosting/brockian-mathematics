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

lemma prefixFreeList_tail (b : Bool) (M : List (List Bool)) (hb : ∀ c ∈ M, c.headI = b)
    (hne : ∀ c ∈ M, c ≠ []) (h : PrefixFreeList M) : PrefixFreeList (M.map List.tail) := by
  rw [PrefixFreeList, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ h
  intro c d hc hd hcd
  have hc' : c = b :: c.tail := by
    have hcb := hb c hc
    cases c with
    | nil => exact absurd rfl (hne _ hc)
    | cons a t => simpa using hcb
  have hd' : d = b :: d.tail := by
    have hdb := hb d hd
    cases d with
    | nil => exact absurd rfl (hne _ hd)
    | cons a t => simpa using hdb
  constructor
  · intro hpre
    exact hcd.1 (by rw [hc', hd']; exact List.cons_prefix_cons.2 ⟨rfl, hpre⟩)
  · intro hpre
    exact hcd.2 (by rw [hc', hd']; exact List.cons_prefix_cons.2 ⟨rfl, hpre⟩)

/-- **Kraft's inequality**: a prefix-free list of codewords satisfies `∑ 2^(-|c|) ≤ 1`. -/
