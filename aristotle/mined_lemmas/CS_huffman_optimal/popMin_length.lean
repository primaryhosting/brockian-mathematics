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

@[simp] lemma popMin_length (f : α → ℝ) (a : α) (l : List α) :
    (popMin f a l).2.length = l.length := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => by_cases h : f b < f a <;> simp [popMin_cons, h, ih]

