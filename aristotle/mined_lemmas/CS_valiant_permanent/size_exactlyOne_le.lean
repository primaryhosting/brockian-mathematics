import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

lemma size_exactlyOne_le (m : ℕ) (f : Fin m → Circuit ι) (B : ℕ) (hf : ∀ a, (f a).size ≤ B) :
    (exactlyOne m f).size ≤ 3 + m * (1 + B) + (m * m) * (3 + 2 * B) := by
  have h1 := size_atLeastOne_le m f B hf
  have h2 := size_atMostOne_le m f B hf
  simp only [exactlyOne, size]
  omega

end Circuit

/-- A counting problem: for each size parameter `n` the instances are bit strings of length
`isize n`, and `count n x` is the number to be computed. -/
structure CountingProblem where
  isize : ℕ → ℕ
  count : (n : ℕ) → (Fin (isize n) → Bool) → ℕ

/-- Polynomial boundedness of a function `ℕ → ℕ`. -/
