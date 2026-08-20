import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem normalize (D : WD) (hw : ∀ p ∈ D, 0 ≤ p.1) (hD : D ≠ 0) (hk : kraft D ≤ 1) :
    ∃ D' : WD, wts D' = wts D ∧ kraft D' = 1 ∧ cost D' ≤ cost D :=
  normalize_aux _ D rfl hw hD hk

end CS

import Mathlib

/-!
# Kraft's inequality for finite prefix-free codes

A finite list of binary codewords is *prefix-free* if no codeword is a prefix of another.
For such a list, `∑ (1/2)^(length u) ≤ 1`.
-/

namespace CS

open scoped BigOperators

/-- A list of binary codewords is prefix-free if no codeword is a prefix of another one.
Note that this forces the codewords to be pairwise distinct. -/
