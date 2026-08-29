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

def cycleAdj10 : Matrix (ZMod 10) (ZMod 10) ℝ :=
  fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- A primitive `10`-th root of unity. -/
