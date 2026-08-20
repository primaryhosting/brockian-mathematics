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

open Matrix Polynomial

namespace Chem

/-! ## A primitive tenth root of unity and the associated additive character -/

/-- A primitive `10`-th root of unity. -/

lemma C10_eq_conj : C10 = (dftUnit : Matrix (ZMod 10) (ZMod 10) ℂ) *
    Matrix.diagonal huckelEigenvalue * (↑dftUnit⁻¹ : Matrix (ZMod 10) (ZMod 10) ℂ) := by
  have h : (↑dftUnit⁻¹ : Matrix (ZMod 10) (ZMod 10) ℂ) = dftMatInv := rfl
  have hU : (dftUnit : Matrix (ZMod 10) (ZMod 10) ℂ) = dftMat := rfl
  rw [h, hU, ← C10_mul_dftMat, mul_assoc, dftMat_mul_dftMatInv, mul_one]

/-! ## Characteristic polynomial and spectrum -/

