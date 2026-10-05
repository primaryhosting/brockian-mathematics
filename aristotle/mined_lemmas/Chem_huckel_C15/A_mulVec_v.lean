import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 15-th root of unity `exp(2πi/15)`. -/

lemma A_mulVec_v (k : ZMod 15) :
    A *ᵥ v k = ((2 : ℂ) * Real.cos (2 * Real.pi * k.val / 15)) • v k := by
  funext i
  rw [A_mulVec, Pi.smul_apply, smul_eq_mul, ← chi_add_chi_neg]
  show chi (k * (i - 1)) + chi (k * (i + 1)) = _
  have e1 : k * (i - 1) = -k + k * i := by ring
  have e2 : k * (i + 1) = k + k * i := by ring
  rw [e1, e2, chi_add, chi_add]
  show _ = (chi k + chi (-k)) * chi (k * i)
  ring

