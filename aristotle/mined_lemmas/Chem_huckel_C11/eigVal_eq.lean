/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Complex Finset

namespace Chem

/-- The circulant form of the adjacency matrix of the cycle graph `C₁₁`,
with vertices indexed by `ZMod 11`. -/

theorem eigVal_eq (k : ZMod 11) :
    eigVal k = ((2 * Real.cos (2 * Real.pi * k.val / 11) : ℝ) : ℂ) := by
  have hk : ((k.val : ℤ) : ZMod 11) = k := by push_cast; simp
  have h1 : ee k = Complex.exp ((2 * Real.pi * k.val / 11 : ℝ) * I) := by
    conv_lhs => rw [← hk]
    rw [ZMod.stdAddChar_coe]
    push_cast
    ring_nf
  rw [eigVal, AddChar.map_neg_eq_inv, h1, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos]
  ring_nf

