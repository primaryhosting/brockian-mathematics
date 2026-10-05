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

theorem adj_mul_C10F : C10adj * C10F = C10F * Matrix.diagonal C10eigen := by
  ext i k
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  have : ∑ j : ZMod 10, C10adj i j * C10F j k
      = (C10adj *ᵥ fun j => C10F j k) i := by
    rw [Matrix.mulVec, dotProduct]
  rw [this, adj_mulVec]
  simp only [C10F, Matrix.of_apply]
  have e1 : (i - 1) * k = i * k + -k := by ring
  have e2 : (i + 1) * k = i * k + k := by ring
  rw [e1, e2, chi_add, chi_add, ← chi_add_neg]
  ring

