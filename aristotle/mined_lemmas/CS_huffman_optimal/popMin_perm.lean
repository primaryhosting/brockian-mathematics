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

lemma popMin_perm (f : α → ℝ) (a : α) (l : List α) :
    (popMin f a l).1 :: (popMin f a l).2 ~ a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
      by_cases h : f b < f a
      · simp only [popMin_cons, h, if_pos]
        exact (List.Perm.swap a _ _).trans ((ih b).cons a)
      · simp only [popMin_cons, h, if_neg, not_false_iff]
        exact ((List.Perm.swap b _ _).trans (((ih a).cons b).trans (List.Perm.swap _ _ _)))

