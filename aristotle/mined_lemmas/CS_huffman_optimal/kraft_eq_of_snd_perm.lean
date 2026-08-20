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

lemma kraft_eq_of_snd_perm {S T : List (ℝ × ℕ)} (h : S.map Prod.snd ~ T.map Prod.snd) :
    kraft S = kraft T := by
  have := (h.map (fun n : ℕ => (2:ℝ)⁻¹ ^ n)).sum_eq
  simpa [kraft, List.map_map, Function.comp] using this

