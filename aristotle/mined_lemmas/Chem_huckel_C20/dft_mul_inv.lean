/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma dft_mul_inv : dftMat * dftMatInv = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [dftMat, dftMatInv, Matrix.of_apply]
  have hkey : ∀ k : ZMod 20, e (i * k) * ((20 : ℂ)⁻¹ * e (-(k * j)))
      = (20 : ℂ)⁻¹ * e ((i - j) * k) := by
    intro k
    have h : (i - j) * k = i * k + -(k * j) := by ring
    rw [h, e_add]
    ring
  simp only [hkey, ← Finset.mul_sum, sum_e (i - j)]
  by_cases hij : i = j
  · simp [hij, Matrix.one_apply]
  · have : i - j ≠ 0 := sub_ne_zero_of_ne hij
    simp [this, hij]

