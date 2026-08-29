/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

lemma dft_mul_inv : dftMat * dftMatInv = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  have : ∀ j : Fin 11, dftMat a j * dftMatInv j b = (11 : ℂ)⁻¹ * echar (j * (a - b)) := by
    intro j
    simp only [dftMat, dftMatInv, Matrix.of_apply]
    have hidx : j * (a - b) = a * j + -(j * b) := by revert a b j; decide
    rw [hidx, echar_add]
    ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, sum_echar]
  by_cases hab : a = b
  · subst hab
    simp
  · have : a - b ≠ 0 := sub_ne_zero_of_ne hab
    simp [this, hab]

