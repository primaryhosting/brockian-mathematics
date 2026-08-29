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

namespace Frontier

open Polynomial

/-! ## Hermite polynomials over `ℝ` -/

/-- The (probabilists') Hermite polynomials, with real coefficients. -/
noncomputable def hermiteR (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

theorem hermite_deriv (n : ℕ) : derivative (hermite (n + 1)) = (n + 1 : ℤ[X]) * hermite n := by
  induction n with
  | zero => simp [hermite_zero]
  | succ n ih =>
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, ih, derivative_mul]
    simp only [derivative_add, derivative_natCast, derivative_one, zero_mul, zero_add]
    rw [hermite_succ n]
    push_cast; ring

theorem hermiteR_succ (n : ℕ) : hermiteR (n + 1) = X * hermiteR n - derivative (hermiteR n) := by
  unfold hermiteR
  rw [hermite_succ, Polynomial.map_sub, Polynomial.map_mul, derivative_map]
  simp

theorem hermiteR_deriv (n : ℕ) :
    derivative (hermiteR (n + 1)) = ((n : ℝ[X]) + 1) * hermiteR n := by
  unfold hermiteR
  rw [derivative_map, hermite_deriv]
  push_cast [Polynomial.map_mul]
  simp

/-- The Hermite differential equation `He'' = X He' - n He`. -/
theorem hermiteR_ode (n : ℕ) :
    derivative (derivative (hermiteR n))
      = X * derivative (hermiteR n) - (n : ℝ[X]) * hermiteR n := by
  cases n with
  | zero => simp [hermiteR, hermite_zero]
  | succ n =>
    rw [hermiteR_deriv, derivative_mul]
    simp only [derivative_add, derivative_natCast, derivative_one, zero_mul, zero_add]
    rw [hermiteR_succ]
    push_cast
    ring

theorem hermiteR_ne_zero (n : ℕ) : hermiteR n ≠ 0 := by
  have h : (hermite n).Monic := hermite_monic n
  simpa [hermiteR] using
    (h.map (Int.castRingHom ℝ)).ne_zero

/-! ## Gaussian-damped polynomials -/

/-- `F P x = P(x) · e^{-x²/4}`. -/
noncomputable def F (P : ℝ[X]) : ℝ → ℝ := fun x => P.eval x * Real.exp (-x ^ 2 / 4)

/-- The polynomial operator implementing (twice) the derivative of `F`. -/
noncomputable def R (P : ℝ[X]) : ℝ[X] := 2 * derivative P - X * P

theorem hasDerivAt_F (P : ℝ[X]) (x : ℝ) : HasDerivAt (F P) ((1 / 2) * F (R P) x) x := by
  have h1 : HasDerivAt (fun x : ℝ => P.eval x) (P.derivative.eval x) x := P.hasDerivAt x
  have hg : HasDerivAt (fun x : ℝ => -x ^ 2 / 4) (-x / 2) x := by
    have h := ((hasDerivAt_pow 2 x).neg).div_const 4
    convert h using 1
    push_cast; ring
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 4))
      (Real.exp (-x ^ 2 / 4) * (-x / 2)) x := hg.exp
  have h3 := h1.mul h2
  convert h3 using 1
  simp only [F, R, eval_sub, eval_mul, eval_X, eval_ofNat]
  ring

theorem R_R_hermiteR (n : ℕ) :
    R (R (hermiteR n)) = X ^ 2 * hermiteR n - (4 * (n : ℝ[X]) + 2) * hermiteR n := by
  simp only [R, derivative_sub, derivative_mul, derivative_X, derivative_ofNat, hermiteR_ode n]
  ring

/-! ## The oscillator profile `χ_n` -/

/-- The `n`-th (unnormalised) harmonic-oscillator profile `χ_n(x) = He_n(x) e^{-x²/4}`. -/
noncomputable def chi (n : ℕ) : ℝ → ℝ := F (hermiteR n)

/-- First derivative of `χ_n`. -/
noncomputable def chi1 (n : ℕ) : ℝ → ℝ := fun x => (1 / 2) * F (R (hermiteR n)) x

/-- Second derivative of `χ_n`. -/
noncomputable def chi2 (n : ℕ) : ℝ → ℝ := fun x => (1 / 4) * F (R (R (hermiteR n))) x

theorem hasDerivAt_chi (n : ℕ) (x : ℝ) : HasDerivAt (chi n) (chi1 n x) x :=
  hasDerivAt_F (hermiteR n) x

theorem hasDerivAt_chi1 (n : ℕ) (x : ℝ) : HasDerivAt (chi1 n) (chi2 n x) x := by
  have h := (hasDerivAt_F (R (hermiteR n)) x).const_mul (1 / 2 : ℝ)
  convert h using 1
  simp only [chi2]
  ring

/-- The defining second-order ODE: `χ_n'' = (x²/4 - (n + 1/2)) χ_n`. -/
theorem chi2_eq (n : ℕ) (x : ℝ) : chi2 n x = (x ^ 2 / 4 - (n + 1 / 2)) * chi n x := by
  simp only [chi2, chi, F, R_R_hermiteR, eval_sub, eval_mul, eval_pow, eval_X, eval_add,
    eval_natCast, eval_ofNat]
  ring

/-! ## The magnetic Hamiltonian in Landau gauge -/

/-- Kinetic momentum in the `x`-direction: `π_x = -iℏ ∂_x`. -/
noncomputable def piX (hbar : ℝ) (f : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x y => -Complex.I * (hbar : ℂ) * deriv (fun t => f t y) x

/-- Kinetic momentum in the `y`-direction in Landau gauge `A = (0, Bx, 0)`:
`π_y = -iℏ ∂_y - qBx`. -/
noncomputable def piY (hbar q B : ℝ) (f : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x y => -Complex.I * (hbar : ℂ) * deriv (fun t => f x t) y - ((q * B * x : ℝ) : ℂ) * f x y

/-- The Hamiltonian `H = (π_x² + π_y²) / (2m)` of a particle of mass `m` and charge `q`
in a uniform magnetic field `B` (Landau gauge). -/
noncomputable def landauH (m hbar q B : ℝ) (f : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x y => (1 / (2 * (m : ℂ))) * (piX hbar (piX hbar f) x y + piY hbar q B (piY hbar q B f) x y)

/-- The magnetic length. -/
noncomputable def landauL (hbar q B : ℝ) : ℝ := Real.sqrt (hbar / (2 * (q * B)))

/-- The guiding centre. -/
noncomputable def landauX0 (hbar q B k : ℝ) : ℝ := hbar * k / (q * B)

/-- The `n`-th Landau eigenfunction with transverse wavenumber `k`. -/
noncomputable def landauPsi (hbar q B k : ℝ) (n : ℕ) : ℝ → ℝ → ℂ :=
  fun x y => Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) *
    ((chi n ((x - landauX0 hbar q B k) / landauL hbar q B) : ℝ) : ℂ)

/-! ## Main theorem -/

section

variable {m hbar q B k : ℝ} {n : ℕ}

noncomputable def phiR (hbar q B k : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => chi n ((x - landauX0 hbar q B k) / landauL hbar q B)

noncomputable def dphiR (hbar q B k : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => (1 / landauL hbar q B) * chi1 n ((x - landauX0 hbar q B k) / landauL hbar q B)

noncomputable def ddphiR (hbar q B k : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => (1 / landauL hbar q B) ^ 2 * chi2 n ((x - landauX0 hbar q B k) / landauL hbar q B)

theorem landauL_pos (hhbar : 0 < hbar) (hqB : 0 < q * B) : 0 < landauL hbar q B :=
  Real.sqrt_pos.mpr (by positivity)

theorem landauL_sq (hhbar : 0 < hbar) (hqB : 0 < q * B) :
    landauL hbar q B ^ 2 = hbar / (2 * (q * B)) :=
  Real.sq_sqrt (by positivity)

theorem hasDerivAt_phiR (hhbar : 0 < hbar) (hqB : 0 < q * B) (x : ℝ) :
    HasDerivAt (phiR hbar q B k n) (dphiR hbar q B k n x) x := by
  have hL : landauL hbar q B ≠ 0 := (landauL_pos hhbar hqB).ne'
  have haff : HasDerivAt (fun t : ℝ => (t - landauX0 hbar q B k) / landauL hbar q B)
      (1 / landauL hbar q B) x := by
    have := ((hasDerivAt_id x).sub_const (landauX0 hbar q B k)).div_const (landauL hbar q B)
    simpa using this
  have h := (hasDerivAt_chi n ((x - landauX0 hbar q B k) / landauL hbar q B)).comp x haff
  simpa [phiR, dphiR, Function.comp, mul_comm] using h

theorem hasDerivAt_dphiR (hhbar : 0 < hbar) (hqB : 0 < q * B) (x : ℝ) :
    HasDerivAt (dphiR hbar q B k n) (ddphiR hbar q B k n x) x := by
  have hL : landauL hbar q B ≠ 0 := (landauL_pos hhbar hqB).ne'
  have haff : HasDerivAt (fun t : ℝ => (t - landauX0 hbar q B k) / landauL hbar q B)
      (1 / landauL hbar q B) x := by
    have := ((hasDerivAt_id x).sub_const (landauX0 hbar q B k)).div_const (landauL hbar q B)
    simpa using this
  have h := ((hasDerivAt_chi1 n ((x - landauX0 hbar q B k) / landauL hbar q B)).comp x
    haff).const_mul (1 / landauL hbar q B)
  unfold dphiR ddphiR
  simpa [Function.comp, sq, mul_comm, mul_assoc, mul_left_comm] using h


/-! ### Unfolding lemmas for the momentum operators -/

theorem piX_apply (hbar : ℝ) (f : ℝ → ℝ → ℂ) (x y : ℝ) :
    piX hbar f x y = -Complex.I * (hbar : ℂ) * deriv (fun t : ℝ => f t y) x := rfl

theorem piY_apply (hbar q B : ℝ) (f : ℝ → ℝ → ℂ) (x y : ℝ) :
    piY hbar q B f x y
      = -Complex.I * (hbar : ℂ) * deriv (fun t : ℝ => f x t) y
        - ((q * B * x : ℝ) : ℂ) * f x y := rfl

theorem landauH_apply (m hbar q B : ℝ) (f : ℝ → ℝ → ℂ) (x y : ℝ) :
    landauH m hbar q B f x y
      = (1 / (2 * (m : ℂ))) *
        (piX hbar (piX hbar f) x y + piY hbar q B (piY hbar q B f) x y) := rfl

theorem landauPsi_eq_phiR (x y : ℝ) :
    landauPsi hbar q B k n x y
      = Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((phiR hbar q B k n x : ℝ) : ℂ) := rfl

/-! ### The `x`-momentum -/

theorem deriv_x_landauPsi (hhbar : 0 < hbar) (hqB : 0 < q * B) (x y : ℝ) :
    deriv (fun t : ℝ => landauPsi hbar q B k n t y) x
      = Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((dphiR hbar q B k n x : ℝ) : ℂ) :=
  (((hasDerivAt_phiR (k := k) (n := n) hhbar hqB x).ofReal_comp).const_mul
    (Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)))).deriv

theorem piX_landauPsi (hhbar : 0 < hbar) (hqB : 0 < q * B) (x y : ℝ) :
    piX hbar (landauPsi hbar q B k n) x y
      = -Complex.I * (hbar : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ))
        * ((dphiR hbar q B k n x : ℝ) : ℂ) := by
  rw [piX_apply, deriv_x_landauPsi hhbar hqB]
  ring

theorem piX_piX_landauPsi (hhbar : 0 < hbar) (hqB : 0 < q * B) (x y : ℝ) :
    piX hbar (piX hbar (landauPsi hbar q B k n)) x y
      = -((hbar : ℂ) ^ 2) * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ))
        * ((ddphiR hbar q B k n x : ℝ) : ℂ) := by
  have hfun : (fun t : ℝ => piX hbar (landauPsi hbar q B k n) t y)
      = fun t : ℝ => (-Complex.I * (hbar : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)))
        * ((dphiR hbar q B k n t : ℝ) : ℂ) := by
    funext t
    rw [piX_landauPsi hhbar hqB]
  have hd : deriv (fun t : ℝ => piX hbar (landauPsi hbar q B k n) t y) x
      = (-Complex.I * (hbar : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)))
        * ((ddphiR hbar q B k n x : ℝ) : ℂ) := by
    rw [hfun]
    exact (((hasDerivAt_dphiR (k := k) (n := n) hhbar hqB x).ofReal_comp).const_mul _).deriv
  rw [piX_apply, hd]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination ((hbar : ℂ) ^ 2 * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ))
    * ((ddphiR hbar q B k n x : ℝ) : ℂ)) * hI

/-! ### The `y`-momentum -/

theorem hasDerivAt_cexp_lin (k y : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (k : ℂ) * (t : ℂ)))
      (Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * (Complex.I * (k : ℂ))) y := by
  have h0 : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 y := (hasDerivAt_id y).ofReal_comp
  simpa using (h0.const_mul (Complex.I * (k : ℂ))).cexp

theorem deriv_y_landauPsi (x y : ℝ) :
    deriv (fun t : ℝ => landauPsi hbar q B k n x t) y
      = Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * (Complex.I * (k : ℂ))
        * ((phiR hbar q B k n x : ℝ) : ℂ) :=
  ((hasDerivAt_cexp_lin k y).mul_const ((phiR hbar q B k n x : ℝ) : ℂ)).deriv

theorem piY_landauPsi (x y : ℝ) :
    piY hbar q B (landauPsi hbar q B k n) x y
      = ((hbar * k - q * B * x : ℝ) : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ))
        * ((phiR hbar q B k n x : ℝ) : ℂ) := by
  rw [piY_apply, deriv_y_landauPsi, landauPsi_eq_phiR]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  linear_combination (-((hbar : ℂ) * (k : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ))
    * ((phiR hbar q B k n x : ℝ) : ℂ))) * hI

theorem piY_piY_landauPsi (x y : ℝ) :
    piY hbar q B (piY hbar q B (landauPsi hbar q B k n)) x y
      = ((hbar * k - q * B * x : ℝ) : ℂ) ^ 2 * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ))
        * ((phiR hbar q B k n x : ℝ) : ℂ) := by
  have hfun : (fun t : ℝ => piY hbar q B (landauPsi hbar q B k n) x t)
      = fun t : ℝ => ((hbar * k - q * B * x : ℝ) : ℂ)
          * Complex.exp (Complex.I * (k : ℂ) * (t : ℂ))
          * ((phiR hbar q B k n x : ℝ) : ℂ) := funext fun t => piY_landauPsi x t
  have hd : deriv (fun t : ℝ => piY hbar q B (landauPsi hbar q B k n) x t) y
      = ((hbar * k - q * B * x : ℝ) : ℂ)
        * (Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * (Complex.I * (k : ℂ)))
        * ((phiR hbar q B k n x : ℝ) : ℂ) := by
    rw [hfun]
    exact (((hasDerivAt_cexp_lin k y).const_mul ((hbar * k - q * B * x : ℝ) : ℂ)).mul_const
      ((phiR hbar q B k n x : ℝ) : ℂ)).deriv
  rw [piY_apply, hd, piY_landauPsi]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  linear_combination (-((hbar : ℂ) * (k : ℂ) * ((hbar : ℂ) * (k : ℂ)
    - (q : ℂ) * (B : ℂ) * (x : ℂ)) * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ))
    * ((phiR hbar q B k n x : ℝ) : ℂ))) * hI

/-! ### The scalar identity -/

theorem landau_real_key (hm : 0 < m) (hhbar : 0 < hbar) (hqB : 0 < q * B) (x : ℝ) :
    (1 / (2 * m)) * (-(hbar ^ 2) * ddphiR hbar q B k n x
        + (hbar * k - q * B * x) ^ 2 * phiR hbar q B k n x)
      = hbar * (q * B / m) * (n + 1 / 2) * phiR hbar q B k n x := by
  have hL : landauL hbar q B ≠ 0 := (landauL_pos hhbar hqB).ne'
  have hL2 : landauL hbar q B ^ 2 = hbar / (2 * (q * B)) := landauL_sq hhbar hqB
  have hh0 : hbar ≠ 0 := hhbar.ne'
  have hqB0 : q * B ≠ 0 := hqB.ne'
  have hq0 : q ≠ 0 := fun h => hqB0 (by simp [h])
  have hB0 : B ≠ 0 := fun h => hqB0 (by simp [h])
  have hm0 : m ≠ 0 := hm.ne'
  have hA : (1 / landauL hbar q B) ^ 2 = 2 * (q * B) / hbar := by
    rw [div_pow, one_pow, hL2]
    field_simp
  have hBsq : ((x - landauX0 hbar q B k) / landauL hbar q B) ^ 2
      = (x - landauX0 hbar q B k) ^ 2 * (2 * (q * B) / hbar) := by
    rw [div_pow, hL2]
    field_simp
  have hscalar : (1 / (2 * m)) * (-(hbar ^ 2) * ((1 / landauL hbar q B) ^ 2 *
        (((x - landauX0 hbar q B k) / landauL hbar q B) ^ 2 / 4 - ((n : ℝ) + 1 / 2)))
        + (hbar * k - q * B * x) ^ 2)
      = hbar * (q * B / m) * ((n : ℝ) + 1 / 2) := by
    rw [hA, hBsq, landauX0]
    field_simp
    ring
  simp only [ddphiR, chi2_eq, phiR]
  linear_combination (chi n ((x - landauX0 hbar q B k) / landauL hbar q B)) * hscalar

end

/-- **Landau levels.**  A charged particle of mass `m > 0` and charge `q` moving in the plane
in a uniform perpendicular magnetic field `B` (with `qB > 0`), described in the Landau gauge
by the Hamiltonian `H = ((-iℏ∂_x)² + (-iℏ∂_y - qBx)²)/(2m)`, has, for every `n : ℕ` and every
transverse wavenumber `k`, an eigenfunction `landauPsi` with eigenvalue `ℏ ω_c (n + 1/2)`,
where `ω_c = qB/m` is the cyclotron frequency. -/
theorem landau_levels (m hbar q B k : ℝ) (n : ℕ)
    (hm : 0 < m) (hhbar : 0 < hbar) (hqB : 0 < q * B) (x y : ℝ) :
    landauH m hbar q B (landauPsi hbar q B k n) x y
      = ((hbar * (q * B / m) * (n + 1 / 2) : ℝ) : ℂ) * landauPsi hbar q B k n x y := by
  have hK := congrArg (fun r : ℝ => (r : ℂ)) (landau_real_key (k := k) (n := n) hm hhbar hqB x)
  simp only at hK
  push_cast at hK
  rw [landauH_apply, piX_piX_landauPsi hhbar hqB, piY_piY_landauPsi, landauPsi_eq_phiR]
  push_cast
  linear_combination Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * hK

/-- The Landau eigenfunctions are not identically zero, so the eigenvalue relation above
is not vacuous. -/
theorem landauPsi_ne_zero (hbar q B k : ℝ) (n : ℕ) (hhbar : 0 < hbar) (hqB : 0 < q * B) :
    ∃ x y : ℝ, landauPsi hbar q B k n x y ≠ 0 := by
  have hL : landauL hbar q B ≠ 0 := (landauL_pos hhbar hqB).ne'
  obtain ⟨t, ht⟩ : ∃ t : ℝ, (hermiteR n).eval t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hermiteR_ne_zero n (Polynomial.funext (fun r => by simpa using h r))
  refine ⟨t * landauL hbar q B + landauX0 hbar q B k, 0, ?_⟩
  have harg : (t * landauL hbar q B + landauX0 hbar q B k - landauX0 hbar q B k)
      / landauL hbar q B = t := by
    rw [add_sub_cancel_right]
    field_simp
  simp only [landauPsi, harg, chi, F]
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (Complex.ofReal_ne_zero.mpr (mul_ne_zero ht (Real.exp_ne_zero _)))

end Frontier

