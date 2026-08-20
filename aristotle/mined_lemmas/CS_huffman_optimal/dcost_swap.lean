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

lemma dcost_swap (x y : ℝ) (m d : ℕ) (T : List (ℝ × ℕ)) (hxy : x ≤ y) (hdm : d ≤ m) :
    dcost ((x, m) :: (y, d) :: T) ≤ dcost ((x, d) :: (y, m) :: T) := by
  simp only [dcost_cons]
  have h1 : (0:ℝ) ≤ (y - x) * ((m : ℝ) - d) := by
    have : (d : ℝ) ≤ m := by exact_mod_cast hdm
    nlinarith
  nlinarith

/-! ## The maximal depth can be assumed to occur twice -/

