/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring; the header above is
-- repeated below as the module docstring.)
import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Finset

namespace Chem

/-- The standard additive character of `ZMod 11`, `x ↦ exp (2πI x / 11)`. -/
local notation "χ" => (ZMod.stdAddChar : AddChar (ZMod 11) ℂ)

/-- The Hückel eigenvalues of the cycle `C₁₁`. -/

lemma Gmat_mul_Fmat : Gmat * Fmat = 1 := by
  ext k k'
  have : ∀ j : ZMod 11, Gmat k j * Fmat j k' = (11 : ℂ)⁻¹ * χ ((k' - k) * j) := by
    intro j
    simp only [Gmat, Fmat, Matrix.of_apply]
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    ring_nf
  rw [Matrix.mul_apply]
  simp only [this, ← Finset.mul_sum, sum_char]
  by_cases h : k = k'
  · subst h; simp
  · rw [if_neg (by simpa [sub_eq_zero] using fun hh => h hh.symm),
      Matrix.one_apply_ne h]
    simp

