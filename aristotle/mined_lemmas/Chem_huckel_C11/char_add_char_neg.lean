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

lemma char_add_char_neg (k : ZMod 11) : χ k + χ (-k) = lam k := by
  have h1 : χ k = Complex.exp ((2 * Real.pi * k.val / 11 : ℝ) * I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    push_cast
    ring_nf
  have h2 : χ (-k) = Complex.exp (-((2 * Real.pi * k.val / 11 : ℝ) * I)) := by
    have hmul : χ k * χ (-k) = 1 := by
      rw [← AddChar.map_add_eq_mul]; simp
    have hne : χ k ≠ 0 := by
      rw [h1]; exact Complex.exp_ne_zero _
    have : χ (-k) = (χ k)⁻¹ := by
      field_simp at hmul ⊢
      linear_combination hmul
    rw [this, h1, ← Complex.exp_neg]
  rw [h1, h2, lam, Complex.ofReal_cos, Complex.cos]
  ring_nf

