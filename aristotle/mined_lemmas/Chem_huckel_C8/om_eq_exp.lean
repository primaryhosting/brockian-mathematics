/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `ZMod 8`
(vertex `i` is adjacent to `i + 1` and `i - 1`), with complex entries. -/

lemma om_eq_exp (x : ZMod 8) :
    om x = Complex.exp ((((2 * Real.pi * (x.val : ℝ) / 8 : ℝ)) : ℂ) * Complex.I) := by
  rw [om, zeta8, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The character values combine into the Hückel eigenvalue `2 cos (2πk/8)`. -/
