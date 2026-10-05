import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

theorem chi_mul_pow (k m : ZMod 10) : chi (k * m) = (chi m) ^ k.val := by
  have h : chi (k * m) = chi (((k.val * m.val : ℕ) : ZMod 10)) := by congr 1
  rw [h, chi_natCast, chi, ← pow_mul, mul_comm]

