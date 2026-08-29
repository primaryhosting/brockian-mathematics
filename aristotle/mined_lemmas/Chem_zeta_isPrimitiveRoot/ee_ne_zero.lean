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

lemma ee_ne_zero (x : ZMod 13) : ee x ≠ 0 := by
  have : zeta ≠ 0 := by
    simp [zeta, Complex.exp_ne_zero]
  exact pow_ne_zero _ this

