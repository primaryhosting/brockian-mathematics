import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex SimpleGraph

namespace Chem

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₄`, i.e. the Hückel matrix of the
carbon skeleton of a 14-membered annulene in units where `α = 0` and `β = 1`. -/

private lemma chi_add_chi_neg (k : ZMod 14) :
    chi k + chi (-k) = 2 * Real.cos (2 * π * k.val / 14) := by
  have h1 : chi k = Complex.exp ((2 * π * k.val / 14 : ℝ) * I) := by
    rw [chi, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    push_cast; ring_nf
  have h2 : chi (-k) = (chi k)⁻¹ := AddChar.map_neg_eq_inv _ _
  rw [h2, h1, ← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I,
    ← Complex.ofReal_neg, ← Complex.ofReal_cos, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast; ring

/-- Translation rule for the discrete Fourier transform on `ZMod 14`. -/
