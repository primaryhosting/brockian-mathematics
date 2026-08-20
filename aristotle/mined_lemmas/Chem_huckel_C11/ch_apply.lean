import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₁`, with vertices indexed by `ZMod 11`:
vertex `i` is adjacent to `i + 1` and `i - 1`. -/

lemma ch_apply (j : ZMod 11) :
    ch j = Complex.exp (2 * Real.pi * Complex.I * j.val / 11) := by
  simpa using ZMod.toCircle_apply (N := 11) j

