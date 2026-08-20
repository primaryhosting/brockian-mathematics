/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial

namespace Frontier

noncomputable section

/-! ## Hermite polynomials over `ℝ` -/

/-- The `n`-th probabilists' Hermite polynomial, viewed as a real polynomial. -/
noncomputable def He (n : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)

lemma derivative_hermite_succ (n : ℕ) :
    derivative (Polynomial.hermite (n + 1)) = C ((n : ℤ) + 1) * Polynomial.hermite n := by
  induction n with
  | zero => simp [Polynomial.hermite_one]
  | succ n ih =>
      rw [Polynomial.hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, ih]
      rw [derivative_mul, derivative_C, Polynomial.hermite_succ n]
      push_cast
      ring
  
lemma He_succ (n : ℕ) : He (n + 1) = X * He n - derivative (He n) := by
  simp [He, Polynomial.hermite_succ, Polynomial.derivative_map]

lemma He_derivative_succ (n : ℕ) : derivative (He (n + 1)) = C ((n : ℝ) + 1) * He n := by
  simp only [He, ← Polynomial.derivative_map, derivative_hermite_succ]
  simp

/-- Hermite's differential equation: `He'' - x He' + n He = 0`. -/
lemma He_ode (n : ℕ) :
    derivative (derivative (He n)) - X * derivative (He n) + C (n : ℝ) * He n = 0 := by
  have h := congrArg derivative (He_succ n)
  rw [He_derivative_succ n, derivative_sub, derivative_mul, derivative_X] at h
  have := h
  linear_combination (norm := ring_nf) -this

/-! ## Gaussian-times-polynomial states -/

/-- A polynomial multiplied by the Gaussian `exp (-x²/4)`. -/
noncomputable def gaussPoly (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  P.eval x * Real.exp (-(x ^ 2 / 4))

/-- The derivative operator maps `gaussPoly P` to `gaussPoly (P' - x P / 2)`. -/
lemma hasDerivAt_gaussPoly (P : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (gaussPoly P) (gaussPoly (derivative P - C (1 / 2 : ℝ) * X * P) x) x := by
  have h1 : HasDerivAt (fun y : ℝ => P.eval y) ((derivative P).eval x) x := P.hasDerivAt x
  have h2 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 4)) (-(x / 2)) x := by
    have : HasDerivAt (fun y : ℝ => y ^ 2 / 4) (2 * x / 4) x := by
      simpa using ((hasDerivAt_pow 2 x).div_const 4)
    simpa [neg_div] using this.neg.congr_deriv (by ring)
  have h3 : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 4)))
      (-(x / 2) * Real.exp (-(x ^ 2 / 4))) x := by
    simpa [mul_comm] using h2.exp
  have := h1.mul h3
  refine this.congr_deriv ?_
  simp [gaussPoly]
  ring

lemma deriv_gaussPoly (P : Polynomial ℝ) :
    deriv (gaussPoly P) = gaussPoly (derivative P - C (1 / 2 : ℝ) * X * P) :=
  funext fun x => (hasDerivAt_gaussPoly P x).deriv

/-! ## Landau levels -/

/-- The `n`-th Landau/oscillator eigenstate (in dimensionless coordinates). -/
noncomputable def landauState (n : ℕ) (x : ℝ) : ℝ := gaussPoly (He n) x

/-- The eigenstates are not identically zero. -/
lemma landauState_ne_zero (n : ℕ) : landauState n ≠ 0 := by
  intro h
  have hHe : He n ≠ 0 := by
    have : (Polynomial.hermite n).Monic := Polynomial.hermite_monic n
    simpa [He, Polynomial.map_eq_zero_iff (Int.cast_injective (α := ℝ))] using this.ne_zero
  obtain ⟨x, hx⟩ : ∃ x : ℝ, (He n).eval x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hHe (Polynomial.funext (fun x => by simp [hc x]))
  have := congrFun h x
  simp [landauState, gaussPoly, Real.exp_ne_zero] at this
  exact hx this

/-- **Landau levels.** A charged particle in a uniform magnetic field reduces, in the
dimensionless coordinate `x`, to a harmonic oscillator with Hamiltonian
`H = ℏ ω_c (-d²/dx² + x²/4)`.  The states `landauState n` (Hermite functions) are
eigenfunctions of `H` with eigenvalue `ℏ ω_c (n + 1/2)`: the Landau level spectrum. -/
theorem landau_levels (hbar omega : ℝ) (n : ℕ) (x : ℝ) :
    hbar * omega * (-deriv (deriv (landauState n)) x + x ^ 2 / 4 * landauState n x) =
      hbar * omega * ((n : ℝ) + 1 / 2) * landauState n x := by
  have key : -deriv (deriv (landauState n)) x + x ^ 2 / 4 * landauState n x
      = ((n : ℝ) + 1 / 2) * landauState n x := by
    have hd : deriv (deriv (landauState n)) = gaussPoly
        (derivative (derivative (He n) - C (1 / 2 : ℝ) * X * He n)
          - C (1 / 2 : ℝ) * X * (derivative (He n) - C (1 / 2 : ℝ) * X * He n)) := by
      show deriv (deriv (gaussPoly (He n))) = _
      rw [deriv_gaussPoly, deriv_gaussPoly]
    rw [hd]
    have hpoly : -(derivative (derivative (He n) - C (1 / 2 : ℝ) * X * He n)
          - C (1 / 2 : ℝ) * X * (derivative (He n) - C (1 / 2 : ℝ) * X * He n))
        + C (1 / 4 : ℝ) * X ^ 2 * He n = C ((n : ℝ) + 1 / 2) * He n := by
      have h := He_ode n
      rw [derivative_sub, derivative_mul, derivative_mul, derivative_C, derivative_X]
      rw [C_add]
      linear_combination (norm := ring_nf) h
    have := congrArg (fun P => gaussPoly P x) hpoly
    simp only [gaussPoly, eval_add, eval_neg, eval_mul, eval_pow, eval_X, eval_C] at this ⊢
    simp only [landauState, gaussPoly]
    nlinarith [this, Real.exp_pos (-(x ^ 2 / 4))]
  rw [mul_assoc, key]
  ring

end

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

