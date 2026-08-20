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

def PrefixFreeList (L : List (List Bool)) : Prop :=
  L.Pairwise fun c d => ¬ c <+: d ∧ ¬ d <+: c

/-- A code (assignment of codewords to symbols) is a prefix code. -/
