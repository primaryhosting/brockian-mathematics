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

lemma ks_nonneg (L : List (List Bool)) : 0 ≤ ks L := by
  refine List.sum_nonneg ?_
  intro x hx
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  positivity

