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

lemma kraft_mul_pow (m : ℕ) : ∀ (S : List (ℝ × ℕ)), (∀ p ∈ S, p.2 ≤ m) →
    (2:ℝ)^m * kraft S = ((S.map fun p => 2^(m - p.2)).sum : ℕ) := by
  intro S
  induction S with
  | nil => simp [kraft]
  | cons p S ih =>
      intro h
      have hp : p.2 ≤ m := h p (by simp)
      have key : (2:ℝ)^m * (2⁻¹)^p.2 = 2^(m - p.2) := by
        rw [pow_sub₀ (2:ℝ) (by norm_num) hp, inv_pow]
      have hIH := ih (fun q hq => h q (by simp [hq]))
      rw [kraft_cons, mul_add, key, hIH]
      simp only [List.map_cons, List.sum_cons]
      push_cast
      ring

/-- If the maximal depth `m` occurs only once, the Kraft sum leaves room to shorten it. -/
