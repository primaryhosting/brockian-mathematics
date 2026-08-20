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

lemma popMin_cons (f : α → ℝ) (a b : α) (l : List α) :
    popMin f a (b :: l) =
      if f b < f a then ((popMin f b l).1, a :: (popMin f b l).2)
      else ((popMin f a l).1, b :: (popMin f a l).2) := rfl

