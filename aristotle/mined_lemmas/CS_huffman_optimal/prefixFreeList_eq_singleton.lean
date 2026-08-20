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

lemma prefixFreeList_eq_singleton {L : List (List Bool)} (hpf : PrefixFreeList L)
    (hnil : [] ∈ L) : L = [[]] := by
  have hp : L ~ [] :: L.erase [] := List.perm_cons_erase hnil
  have hpf' : PrefixFreeList ([] :: L.erase []) :=
    (List.Perm.pairwise_iff prefixFreeList_symm hp).1 hpf
  have he : L.erase ([] : List Bool) = [] := by
    rcases e : L.erase ([] : List Bool) with _ | ⟨d, R⟩
    · rfl
    · exfalso
      rw [e] at hpf'
      exact ((List.pairwise_cons.1 hpf').1 d (by simp)).1 (List.nil_prefix)
  rw [he] at hp
  exact List.perm_singleton.1 hp

