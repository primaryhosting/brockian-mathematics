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

lemma ks_tail (M : List (List Bool)) (hne : ∀ c ∈ M, c ≠ []) :
    ks M = 2⁻¹ * ks (M.map List.tail) := by
  induction M with
  | nil => simp [ks]
  | cons c M ih =>
      have hc : c ≠ [] := hne c (by simp)
      have hlen : c.length = c.tail.length + 1 := by
        cases c with
        | nil => exact absurd rfl hc
        | cons a t => simp
      have ih' := ih (fun d hd => hne d (by simp [hd]))
      simp only [ks, List.map_cons, List.sum_cons, hlen, pow_succ] at *
      rw [ih']
      ring

