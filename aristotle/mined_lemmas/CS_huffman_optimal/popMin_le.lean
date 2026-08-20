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

lemma popMin_le (f : α → ℝ) (a : α) (l : List α) :
    ∀ x ∈ a :: l, f (popMin f a l).1 ≤ f x := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
      intro x hx
      by_cases h : f b < f a
      · simp only [popMin_cons, h, if_pos]
        have h1 := ih b
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact le_trans (h1 b (by simp)) h.le
        · exact h1 x hx'
      · simp only [popMin_cons, h, if_neg, not_false_iff]
        have h1 := ih a
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact h1 x (by simp)
        · rcases List.mem_cons.1 hx' with rfl | hx''
          · exact le_trans (h1 a (by simp)) (not_lt.1 h)
          · exact h1 x (by simp [hx''])

