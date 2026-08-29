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

lemma zeta_prim : IsPrimitiveRoot zeta 10 := by
  simpa [zeta] using Complex.isPrimitiveRoot_exp 10 (by norm_num)

