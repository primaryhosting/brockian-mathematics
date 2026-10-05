import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/

lemma sum_ee : ∑ k : ZMod 13, ee k = 0 := by
  have := sum_zmod_val (fun j => zeta ^ j)
  simpa [ee] using this.trans (zeta_isPrimitiveRoot.geom_sum_eq_zero (by norm_num))

