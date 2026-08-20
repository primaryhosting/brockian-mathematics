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

lemma popMin_map (f : α → ℝ) (a : α) (l : List α) :
    f (popMin f a l).1 = (popMin id (f a) (l.map f)).1 ∧
      (popMin f a l).2.map f = (popMin id (f a) (l.map f)).2 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
      by_cases h : f b < f a
      · simp only [popMin_cons, h, if_pos, List.map_cons]
        have : (id (f b) : ℝ) < id (f a) := h
        simp only [this, if_pos]
        exact ⟨(ih b).1, by simp [(ih b).2]⟩
      · simp only [popMin_cons, h, if_neg, not_false_iff, List.map_cons]
        have : ¬ ((id (f b) : ℝ) < id (f a)) := h
        simp only [this, if_neg, not_false_iff]
        exact ⟨(ih a).1, by simp [(ih a).2]⟩

/-! ## Codes -/

/-- The total weight of a group of symbols. -/
