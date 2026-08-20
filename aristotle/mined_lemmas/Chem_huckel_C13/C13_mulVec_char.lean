import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/

lemma C13_mulVec_char (k : ZMod 13) :
    C13 *ᵥ (fun j => e13 (k * j))
      = ((huckelEigenvalue k.val : ℝ) : ℂ) • (fun j => e13 (k * j)) := by
  funext i
  rw [C13_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : e13 (k * (i + 1)) = e13 (k * i) * e13 k := by
    rw [mul_add, mul_one, e13_add]
  have h2 : e13 (k * (i - 1)) = e13 (k * i) * (e13 k)⁻¹ := by
    rw [mul_sub, mul_one, sub_eq_add_neg, e13_add, e13_neg]
  rw [h1, h2, ← e13_add_inv k]
  ring

/-- Fourier inversion on `ZMod 13`. -/
