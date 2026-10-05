import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₀`, with vertices indexed by `ZMod 10`:
`i` and `j` are adjacent iff they differ by `1` modulo `10`. -/

lemma cycleAdj10_mulVec (v : ZMod 10 → ℝ) (i : ZMod 10) :
    cycleAdj10.mulVec v i = v (i - 1) + v (i + 1) := by
  have h : cycleAdj10.mulVec v i
      = ∑ j : ZMod 10, (if i - j = 1 ∨ j - i = 1 then (1 : ℝ) else 0) * v j := rfl
  rw [h, adj_sum]

/-- The discrete Fourier transform is injective on `ZMod 10`-indexed vectors. -/
