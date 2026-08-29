import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset

/-- A primitive 16-th root of unity. -/

lemma huckelEigenvalue_mul (k : ZMod 16) :
    huckelEigenvalue k * zeta ^ k.val = (zeta ^ k.val) ^ 2 + 1 := by
  set t : ℝ := 2 * Real.pi * k.val / 16 with ht
  have hc : zeta ^ k.val = Complex.exp ((t : ℂ) * Complex.I) := zeta_pow_val k
  have h2 : (2 : ℂ) * Complex.cos (t : ℂ)
      = Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-(t : ℂ) * Complex.I) :=
    Complex.two_cos _
  have hinv : Complex.exp (-(t : ℂ) * Complex.I)
      = (Complex.exp ((t : ℂ) * Complex.I))⁻¹ := by
    rw [← Complex.exp_neg]; ring_nf
  have hne : Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hlam : huckelEigenvalue k
      = Complex.exp ((t : ℂ) * Complex.I) + (Complex.exp ((t : ℂ) * Complex.I))⁻¹ := by
    rw [huckelEigenvalue, ← ht, Complex.ofReal_cos, h2, hinv]
  rw [hlam, hc]
  field_simp

