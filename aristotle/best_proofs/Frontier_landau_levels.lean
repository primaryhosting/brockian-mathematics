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

set_option grind.warning false

/-!
# Landau levels

A charged particle of mass `m` and charge `q` moving in the plane in a uniform magnetic field `B`
perpendicular to the plane has energy spectrum `ℏ ω_c (n + 1/2)`, where `ω_c = q B / m` is the
cyclotron frequency.

We work in the Landau gauge `A = (0, B x)`, so that the Hamiltonian is

  `H = (1/(2m)) ( (-iℏ ∂ₓ)² + (-iℏ ∂_y - q B x)² )`
    `= (1/(2m)) ( -ℏ² ∂ₓ² - ℏ² ∂_y² + 2iℏ q B x ∂_y + q²B²x² )`,

which is `Frontier.landauH` below.

The eigenfunctions are `exp (i k y)` times a shifted Hermite function of `x`
(`Frontier.landauState`), and `Frontier.landau_levels` states that these are eigenfunctions of
`landauH` with eigenvalue `ℏ (qB/m) (n + 1/2)`.
-/

namespace Frontier

open Polynomial

/-! ### Hermite polynomial preliminaries -/

/-- The derivative of the (probabilists') Hermite polynomial: `He_{n+1}' = (n+1) He_n`. -/
theorem derivative_hermite (n : ℕ) :
    derivative (hermite (n + 1)) = (n + 1 : ℤ[X]) * hermite n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h2 : derivative ((m + 1 : ℤ[X]) * hermite m) = (m + 1 : ℤ[X]) * derivative (hermite m) := by
      simp [derivative_mul]
    rw [hermite_succ (m + 1), derivative_sub, derivative_mul, derivative_X, ih, h2, hermite_succ m]
    push_cast
    ring

/-- The Hermite differential equation `He_n'' - X He_n' + n He_n = 0`. -/
theorem hermite_ode (n : ℕ) :
    derivative (derivative (hermite n)) - X * derivative (hermite n) + (n : ℤ[X]) * hermite n
      = 0 := by
  cases n with
  | zero => simp
  | succ m =>
    have h2 : derivative ((m + 1 : ℤ[X]) * hermite m) = (m + 1 : ℤ[X]) * derivative (hermite m) := by
      simp [derivative_mul]
    have hx : X * hermite m = hermite (m + 1) + derivative (hermite m) := by
      rw [hermite_succ m]; ring
    have hxx : X * ((m + 1 : ℤ[X]) * hermite m) = (m + 1 : ℤ[X]) * (X * hermite m) := by ring
    rw [derivative_hermite m, h2, hxx, hx]
    push_cast
    ring

/-- The `n`-th probabilists' Hermite polynomial as a real function. -/
noncomputable def He (n : ℕ) (y : ℝ) : ℝ := aeval y (hermite n)

/-- The first derivative of `He n`. -/
noncomputable def He1 (n : ℕ) (y : ℝ) : ℝ := aeval y (derivative (hermite n))

/-- The second derivative of `He n`. -/
noncomputable def He2 (n : ℕ) (y : ℝ) : ℝ := aeval y (derivative (derivative (hermite n)))

theorem hasDerivAt_He (n : ℕ) (y : ℝ) : HasDerivAt (He n) (He1 n y) y :=
  Polynomial.hasDerivAt_aeval _ _

theorem hasDerivAt_He1 (n : ℕ) (y : ℝ) : HasDerivAt (He1 n) (He2 n y) y :=
  Polynomial.hasDerivAt_aeval _ _

theorem He_ode (n : ℕ) (y : ℝ) : He2 n y - y * He1 n y + n * He n y = 0 := by
  have h := congrArg (fun p : ℤ[X] => (aeval y p : ℝ)) (hermite_ode n)
  simpa [He, He1, He2] using h

/-! ### The one-dimensional Hermite functions -/

/-- The `n`-th Hermite function `He_n(y) e^{-y²/4}`, an eigenfunction of `-d²/dy² + y²/4`. -/
noncomputable def hFun (n : ℕ) (y : ℝ) : ℝ := He n y * Real.exp (-(y ^ 2) / 4)

/-- The derivative of `hFun n`. -/
noncomputable def dhFun (n : ℕ) (y : ℝ) : ℝ :=
  (He1 n y - y / 2 * He n y) * Real.exp (-(y ^ 2) / 4)

theorem hasDerivAt_gaussian (y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2) / 4)) (-(y / 2) * Real.exp (-(y ^ 2) / 4)) y := by
  have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2) / 4) (-(y / 2)) y := by
    have h := ((hasDerivAt_pow 2 y).neg).div_const 4
    convert h using 1
    ring
  simpa [mul_comm] using h1.exp

theorem hasDerivAt_hFun (n : ℕ) (y : ℝ) : HasDerivAt (hFun n) (dhFun n y) y := by
  have h := (hasDerivAt_He n y).mul (hasDerivAt_gaussian y)
  refine h.congr_deriv ?_
  simp only [dhFun]
  ring

theorem hasDerivAt_dhFun (n : ℕ) (y : ℝ) :
    HasDerivAt (dhFun n) ((y ^ 2 / 4 - 1 / 2 - n) * hFun n y) y := by
  have hd : HasDerivAt (fun t : ℝ => He1 n t - t / 2 * He n t)
      (He2 n y - (1 / 2 * He n y + y / 2 * He1 n y)) y := by
    have h1 := hasDerivAt_He1 n y
    have h2 := ((hasDerivAt_id y).div_const 2).mul (hasDerivAt_He n y)
    simpa using h1.sub h2
  have h := hd.mul (hasDerivAt_gaussian y)
  refine h.congr_deriv ?_
  have hode := He_ode n y
  simp only [hFun]
  nlinarith [hode, Real.exp_pos (-(y ^ 2) / 4)]

/-! ### The Landau Hamiltonian -/

/-- The Landau Hamiltonian in the Landau gauge `A = (0, B x)`:
`H ψ = (1/(2m)) ( -ℏ² ∂ₓ²ψ - ℏ² ∂_y²ψ + 2iℏ q B x ∂_yψ + q²B²x² ψ )`. -/
noncomputable def landauH (m q B hbar : ℝ) (psi : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  (1 / (2 * (m : ℂ))) *
    (-(hbar : ℂ) ^ 2 * deriv (deriv fun t : ℝ => psi t y) x
      - (hbar : ℂ) ^ 2 * deriv (deriv fun t : ℝ => psi x t) y
      + 2 * Complex.I * (hbar : ℂ) * (q : ℂ) * (B : ℂ) * (x : ℂ) * deriv (fun t : ℝ => psi x t) y
      + ((q : ℂ) * (B : ℂ) * (x : ℂ)) ^ 2 * psi x y)

/-- The magnetic length parameter `b = sqrt (2 q B / ℏ)`. -/
noncomputable def landauB (q B hbar : ℝ) : ℝ := Real.sqrt (2 * q * B / hbar)

/-- The guiding centre `x₀ = ℏ k / (q B)`. -/
noncomputable def landauCentre (q B hbar k : ℝ) : ℝ := hbar * k / (q * B)

/-- The Landau-level eigenstate with transverse momentum `k` and level `n`:
`ψ (x, y) = e^{i k y} He_n(b (x - x₀)) e^{-b²(x-x₀)²/4}`. -/
noncomputable def landauState (q B hbar k : ℝ) (n : ℕ) (x y : ℝ) : ℂ :=
  Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) *
    ((hFun n (landauB q B hbar * (x - landauCentre q B hbar k)) : ℝ) : ℂ)

/-- Action of the Landau Hamiltonian on a state of the form `e^{iky}` times a shifted, scaled
Hermite function. -/
theorem landauH_hermiteState (m q B hbar b x0 k : ℝ) (n : ℕ) (x y : ℝ) :
    landauH m q B hbar
        (fun s t : ℝ => Complex.exp (Complex.I * (k : ℂ) * (t : ℂ)) *
          ((hFun n (b * (s - x0)) : ℝ) : ℂ)) x y
      = ((1 / (2 * m) * (-hbar ^ 2 * (b ^ 2 * ((b * (x - x0)) ^ 2 / 4 - 1 / 2 - n))
            + hbar ^ 2 * k ^ 2 - 2 * hbar * q * B * k * x + (q * B * x) ^ 2) : ℝ) : ℂ)
        * (Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((hFun n (b * (x - x0)) : ℝ) : ℂ)) := by
  have hinner : ∀ t : ℝ, HasDerivAt (fun s : ℝ => b * (s - x0)) b t := by
    intro t
    simpa using ((hasDerivAt_id t).sub_const x0).const_mul b
  have hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => hFun n (b * (s - x0)))
      (b * dhFun n (b * (t - x0))) t := by
    intro t
    simpa [mul_comm] using (hasDerivAt_hFun n (b * (t - x0))).comp t (hinner t)
  have hdF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => b * dhFun n (b * (s - x0)))
      (b ^ 2 * ((b * (t - x0)) ^ 2 / 4 - 1 / 2 - n) * hFun n (b * (t - x0))) t := by
    intro t
    have h := ((hasDerivAt_dhFun n (b * (t - x0))).comp t (hinner t)).const_mul b
    refine h.congr_deriv ?_
    ring
  -- derivatives in the `x` direction
  have hx1 : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((hFun n (b * (s - x0)) : ℝ) : ℂ))
      (Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((b * dhFun n (b * (t - x0)) : ℝ) : ℂ)) t :=
    fun t => ((hF t).ofReal_comp).const_mul _
  have hx1' : (deriv fun s : ℝ =>
        Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((hFun n (b * (s - x0)) : ℝ) : ℂ))
      = fun t : ℝ => Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) *
          ((b * dhFun n (b * (t - x0)) : ℝ) : ℂ) :=
    funext fun t => (hx1 t).deriv
  have hx2 : deriv (deriv fun s : ℝ =>
        Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((hFun n (b * (s - x0)) : ℝ) : ℂ)) x
      = Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) *
          ((b ^ 2 * ((b * (x - x0)) ^ 2 / 4 - 1 / 2 - n) * hFun n (b * (x - x0)) : ℝ) : ℂ) := by
    rw [hx1']
    exact (((hdF x).ofReal_comp).const_mul _).deriv
  -- derivatives in the `y` direction
  have hexp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * (k : ℂ) * (s : ℂ)))
      (Complex.I * (k : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (t : ℂ))) t := by
    intro t
    have h : HasDerivAt (fun s : ℝ => Complex.I * (k : ℂ) * ((s : ℝ) : ℂ))
        (Complex.I * (k : ℂ)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * (k : ℂ))
    simpa [mul_comm] using h.cexp
  have hy1' : (deriv fun s : ℝ =>
        Complex.exp (Complex.I * (k : ℂ) * (s : ℂ)) * ((hFun n (b * (x - x0)) : ℝ) : ℂ))
      = fun t : ℝ => Complex.I * (k : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (t : ℂ)) *
          ((hFun n (b * (x - x0)) : ℝ) : ℂ) :=
    funext fun t => ((hexp t).mul_const _).deriv
  have hy2 : deriv (deriv fun s : ℝ =>
        Complex.exp (Complex.I * (k : ℂ) * (s : ℂ)) * ((hFun n (b * (x - x0)) : ℝ) : ℂ)) y
      = (Complex.I * (k : ℂ)) ^ 2 * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) *
          ((hFun n (b * (x - x0)) : ℝ) : ℂ) := by
    rw [hy1']
    have h := (((hexp y).const_mul (Complex.I * (k : ℂ))).mul_const
      (((hFun n (b * (x - x0)) : ℝ) : ℂ))).deriv
    rw [h]
    ring
  have hy1 : deriv (fun s : ℝ =>
        Complex.exp (Complex.I * (k : ℂ) * (s : ℂ)) * ((hFun n (b * (x - x0)) : ℝ) : ℂ)) y
      = Complex.I * (k : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) *
          ((hFun n (b * (x - x0)) : ℝ) : ℂ) := by
    rw [hy1']
  simp only [landauH, hx2, hy2, hy1]
  push_cast
  linear_combination ((1 / (2 * (m : ℂ))) * (-(hbar : ℂ) ^ 2 * (k : ℂ) ^ 2
      + 2 * (hbar : ℂ) * (q : ℂ) * (B : ℂ) * (x : ℂ) * (k : ℂ))
      * (Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((hFun n (b * (x - x0)) : ℝ) : ℂ)))
    * Complex.I_sq

/-- The energy coefficient collapses to `ℏ ω_c (n + 1/2)`. -/
theorem landau_energy (m q B hbar b x0 k x : ℝ) (n : ℕ) (hm : m ≠ 0) (hq : q ≠ 0) (hB : B ≠ 0)
    (hhbar : hbar ≠ 0) (hb2 : b ^ 2 = 2 * q * B / hbar) (hx0 : x0 = hbar * k / (q * B)) :
    1 / (2 * m) * (-hbar ^ 2 * (b ^ 2 * ((b * (x - x0)) ^ 2 / 4 - 1 / 2 - n))
        + hbar ^ 2 * k ^ 2 - 2 * hbar * q * B * k * x + (q * B * x) ^ 2)
      = hbar * (q * B / m) * (n + 1 / 2) := by
  have hmul : (b * (x - x0)) ^ 2 = b ^ 2 * (x - x0) ^ 2 := by ring
  rw [hmul, hb2, hx0]
  field_simp
  ring

/-- **Landau levels.** A charged particle of mass `m` and charge `q` in a uniform magnetic
field `B` has energy spectrum `ℏ ω_c (n + 1/2)` with cyclotron frequency `ω_c = q B / m`:
the states `landauState` are eigenstates of the Landau Hamiltonian with these energies. -/
theorem landau_levels (m q B hbar : ℝ) (hm : 0 < m) (hq : 0 < q) (hB : 0 < B) (hhbar : 0 < hbar)
    (n : ℕ) (k x y : ℝ) :
    landauH m q B hbar (landauState q B hbar k n) x y
      = ((hbar * (q * B / m) * (n + 1 / 2) : ℝ) : ℂ) * landauState q B hbar k n x y := by
  have hfun : landauState q B hbar k n = fun s t : ℝ =>
      Complex.exp (Complex.I * (k : ℂ) * (t : ℂ)) *
        ((hFun n (landauB q B hbar * (s - landauCentre q B hbar k)) : ℝ) : ℂ) := rfl
  have hb2 : landauB q B hbar ^ 2 = 2 * q * B / hbar :=
    Real.sq_sqrt (by positivity)
  rw [hfun, landauH_hermiteState]
  rw [show ((hbar * (q * B / m) * (n + 1 / 2) : ℝ) : ℂ)
      = ((1 / (2 * m) * (-hbar ^ 2 * (landauB q B hbar ^ 2 *
          ((landauB q B hbar * (x - landauCentre q B hbar k)) ^ 2 / 4 - 1 / 2 - n))
          + hbar ^ 2 * k ^ 2 - 2 * hbar * q * B * k * x + (q * B * x) ^ 2) : ℝ) : ℂ) from ?_]
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ))
    (landau_energy m q B hbar (landauB q B hbar) (landauCentre q B hbar k) k x n
      hm.ne' hq.ne' hB.ne' hhbar.ne' hb2 rfl).symm

/-- The Landau eigenstates are not identically zero, so the eigenvalue equation of
`landau_levels` is not vacuous. -/
theorem landauState_ne_zero (q B hbar k : ℝ) (hq : 0 < q) (hB : 0 < B) (hhbar : 0 < hbar)
    (n : ℕ) : ∃ x y : ℝ, landauState q B hbar k n x y ≠ 0 := by
  have hHe : ∃ y : ℝ, He n y ≠ 0 := by
    by_contra h
    push_neg at h
    have hp : ((hermite n).map (Int.castRingHom ℝ)) ≠ 0 := ((hermite_monic n).map _).ne_zero
    apply hp
    apply Polynomial.funext
    intro y
    simpa [He, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using h y
  obtain ⟨y0, hy0⟩ := hHe
  have hb : 0 < landauB q B hbar := Real.sqrt_pos.mpr (by positivity)
  refine ⟨landauCentre q B hbar k + y0 / landauB q B hbar, 0, ?_⟩
  have hx : landauB q B hbar *
      (landauCentre q B hbar k + y0 / landauB q B hbar - landauCentre q B hbar k) = y0 := by
    field_simp
    ring
  simp only [landauState, hx]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  simpa [hFun, Real.exp_ne_zero] using hy0

end Frontier

