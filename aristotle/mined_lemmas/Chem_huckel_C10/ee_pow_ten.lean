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

lemma ee_pow_ten (m : ZMod 10) : ee m ^ 10 = 1 := by
  rw [ee, ← pow_mul, mul_comm, pow_mul, zeta_pow_ten, one_pow]

/-- Orthogonality relation for the characters of `ZMod 10`. -/
