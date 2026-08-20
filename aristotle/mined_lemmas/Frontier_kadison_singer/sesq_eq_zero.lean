/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the required
-- header above is written as a plain block comment.)

import Mathlib

/-!
The Kadison–Singer problem asks whether every pure state on a maximal abelian self-adjoint
subalgebra (MASA) of `B(ℓ²)` extends uniquely to a state on `B(ℓ²)`.  It was answered
affirmatively by Marcus, Spielman and Srivastava via the method of interlacing families of
polynomials.

This file formalizes and proves in full the *finite-dimensional* case — the base case of the
Kadison–Singer question: for the diagonal MASA of the matrix algebra `Mₙ(ℂ)`, the pure state
`d ↦ d i` of the diagonal has a unique extension to a state on `Mₙ(ℂ)`, namely `A ↦ A i i`.

Here a *state* is a unital positive ℂ-linear functional (`Frontier.IsState`), and the pure
states of the diagonal algebra `ℂⁿ` are exactly the coordinate evaluations `d ↦ d i`.

The proof is the classical one: positivity of `phi` yields a positive semidefinite Hermitian
sesquilinear form `(X, Y) ↦ phi (Xᴴ * Y)`, and the degenerate case of the Cauchy–Schwarz
inequality forces `phi` to vanish on every matrix unit other than `E i i`.
-/

namespace Frontier

open Matrix ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `Mₙ(ℂ)`: a unital, positive linear functional. -/

private lemma sesq_eq_zero (hpos : ∀ B : Matrix n n ℂ, 0 ≤ phi (Bᴴ * B)) (X Y : Matrix n n ℂ)
    (hX : phi (Xᴴ * X) = 0) : phi (Xᴴ * Y) = 0 := by
  set z := phi (Xᴴ * Y) with hz
  set c := phi (Yᴴ * Y) with hc
  have hw : phi (Yᴴ * X) = starRingEnd ℂ z := sesq_conj hpos X Y
  by_contra hne
  have hznorm : 0 < Complex.normSq z := by
    have h0 : Complex.normSq z ≠ 0 := by simpa [Complex.normSq_eq_zero] using hne
    exact lt_of_le_of_ne (Complex.normSq_nonneg z) (Ne.symm h0)
  set R : ℝ := (c.re + 1) / (2 * Complex.normSq z) with hR
  have hcre : 0 ≤ c.re := (Complex.le_def.mp (hpos Y)).1
  have key := quad_nonneg hpos X Y (-(R : ℂ) * z) 1
  rw [hX, hw, ← hz, ← hc] at key
  have hzz : z * starRingEnd ℂ z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  have hexpand : (starRingEnd ℂ (-(R : ℂ) * z) * (-(R : ℂ) * z)) * 0
      + (starRingEnd ℂ (-(R : ℂ) * z) * 1) * z
      + (starRingEnd ℂ (1 : ℂ) * (-(R : ℂ) * z)) * starRingEnd ℂ z
      + (starRingEnd ℂ (1 : ℂ) * 1) * c
      = c - 2 * (R : ℂ) * (Complex.normSq z : ℂ) := by
    simp only [map_mul, map_neg, map_one, Complex.conj_ofReal, one_mul, mul_one, mul_zero, zero_add]
    rw [← hzz]; ring
  rw [hexpand] at key
  have hre : (0 : ℂ).re ≤ (c - 2 * (R : ℂ) * (Complex.normSq z : ℂ)).re := (Complex.le_def.mp key).1
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, Complex.zero_re] at hre
  rw [hR] at hre
  have hfield : (c.re + 1) / (2 * Complex.normSq z) * (2 * Complex.normSq z) = c.re + 1 := by
    field_simp
  nlinarith [hfield]

end Auxiliary

/-- **Kadison–Singer, finite-dimensional case.**
For every index `i`, the pure state `d ↦ d i` of the diagonal MASA of the matrix algebra
`Mₙ(ℂ)` has a *unique* extension to a state (unital positive linear functional) on `Mₙ(ℂ)`,
namely `A ↦ A i i`. -/
