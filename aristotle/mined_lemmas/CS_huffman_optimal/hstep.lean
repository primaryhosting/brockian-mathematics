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

noncomputable def hstep (w : ι → ℝ) :
    List (ι × List Bool) → List (List (ι × List Bool)) → List (ι × List Bool)
  | g, [] => g
  | g, h :: F =>
      hstep w (gmerge (popMin (gw w) g (h :: F)).1
                (popMin (gw w) (popMin (gw w) g (h :: F)).2.headI
                  (popMin (gw w) g (h :: F)).2.tail).1)
            (popMin (gw w) (popMin (gw w) g (h :: F)).2.headI
                  (popMin (gw w) g (h :: F)).2.tail).2
  termination_by _ F => F.length
  decreasing_by
    simp [popMin_length]

/-- The cost of the Huffman code for a list of weights, defined by Huffman's recursion. -/
