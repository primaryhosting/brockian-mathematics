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

def gcost (w : ι → ℝ) (g : List (ι × List Bool)) : ℝ :=
  (g.map fun p => w p.1 * (p.2.length : ℝ)).sum

/-- Merging two groups: prepend `false` to all codewords on the left,
`true` to all codewords on the right. -/
