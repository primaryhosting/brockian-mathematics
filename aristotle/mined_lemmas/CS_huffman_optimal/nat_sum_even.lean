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

lemma nat_sum_even (L : List ℕ) (h : ∀ n ∈ L, n % 2 = 0) : L.sum % 2 = 0 := by
  induction L with
  | nil => simp
  | cons n L ih =>
      have h1 := h n (by simp)
      have h2 := ih (fun k hk => h k (by simp [hk]))
      simp only [List.sum_cons]
      omega

