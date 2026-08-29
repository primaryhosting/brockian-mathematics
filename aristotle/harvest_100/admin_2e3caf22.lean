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

noncomputable section

open Polynomial

/-! ## Probabilists' Hermite polynomials over `ℝ` -/

/-- The `n`-th probabilists' Hermite polynomial, with real coefficients. -/
def Herm (n : ℕ) : Polynomial ℝ := (Polynomial.hermite n).map (Int.castRingHom ℝ)

/-- The `n`-th probabilists' Hermite polynomial as a function `ℝ → ℝ`. -/
def He (n : ℕ) (x : ℝ) : ℝ := (Herm n).eval x

/-- The derivative of `He n`. -/
def He' (n : ℕ) (x : ℝ) : ℝ := (derivative (Herm n)).eval x

/-- The second derivative of `He n`. -/
def He'' (n : ℕ) (x : ℝ) : ℝ := (derivative (derivative (Herm n))).eval x

theorem hermite_derivative_succ (n : ℕ) :
    derivative (hermite (n + 1)) = C ((n : ℤ) + 1) * hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, ih]
    simp only [derivative_X, one_mul, derivative_mul, derivative_C, zero_mul, zero_add]
    rw [hermite_succ n]
    push_cast [C_add, C_1]
    ring

theorem derivative_Herm_succ (n : ℕ) : derivative (Herm (n + 1)) = C ((n : ℝ) + 1) * Herm n := by
  rw [Herm, derivative_map, hermite_derivative_succ, Herm, Polynomial.map_mul, map_C]
  simp

theorem Herm_succ (n : ℕ) : Herm (n + 1) = X * Herm n - derivative (Herm n) := by
  simp [Herm, hermite_succ, Polynomial.derivative_map]

theorem hasDerivAt_He (n : ℕ) (x : ℝ) : HasDerivAt (He n) (He' n x) x :=
  (Herm n).hasDerivAt x

theorem hasDerivAt_He' (n : ℕ) (x : ℝ) : HasDerivAt (He' n) (He'' n x) x :=
  (derivative (Herm n)).hasDerivAt x

theorem He_succ (n : ℕ) (x : ℝ) : He (n + 1) x = x * He n x - He' n x := by
  simp [He, He', Herm_succ n]

theorem He'_succ (n : ℕ) (x : ℝ) : He' (n + 1) x = ((n : ℝ) + 1) * He n x := by
  simp [He, He', derivative_Herm_succ n]

/-- The Hermite differential equation `He'' - x He' + n He = 0`. -/
theorem He_ode (n : ℕ) (x : ℝ) : He'' n x = x * He' n x - n * He n x := by
  cases n with
  | zero => simp [He'', He', He, Herm]
  | succ m =>
    have h1 : He'' (m + 1) x = ((m : ℝ) + 1) * He' m x := by
      simp [He'', He', derivative_Herm_succ m]
    rw [h1, He'_succ, He_succ]
    push_cast
    ring

/-! ## Hermite (Gauss-weighted) functions with length scale `s` -/

/-- The `n`-th Hermite function with length scale `s`:
`u ↦ He n (u/s) * exp (-(u/s)^2/4)`. -/
def hermiteGauss (n : ℕ) (s u : ℝ) : ℝ := He n (u / s) * Real.exp (-(u / s) ^ 2 / 4)

/-- The derivative of `hermiteGauss n s`. -/
def hermiteGaussD (n : ℕ) (s u : ℝ) : ℝ :=
  (He' n (u / s) / s - u / (2 * s ^ 2) * He n (u / s)) * Real.exp (-(u / s) ^ 2 / 4)

theorem hasDerivAt_hermiteGauss (n : ℕ) {s : ℝ} (hs : s ≠ 0) (u : ℝ) :
    HasDerivAt (hermiteGauss n s) (hermiteGaussD n s u) u := by
  have hv : HasDerivAt (fun t : ℝ => t / s) (1 / s) u := by
    simpa using (hasDerivAt_id u).div_const s
  have hHe : HasDerivAt (fun t : ℝ => He n (t / s)) (He' n (u / s) * (1 / s)) u := by
    simpa only [Function.comp_def] using (hasDerivAt_He n (u / s)).comp u hv
  have hq : HasDerivAt (fun t : ℝ => -(t / s) ^ 2 / 4) (-(2 * (u / s) ^ 1 * (1 / s)) / 4) u :=
    ((hv.pow 2).neg).div_const 4
  have hE : HasDerivAt (fun t : ℝ => Real.exp (-(t / s) ^ 2 / 4))
      (Real.exp (-(u / s) ^ 2 / 4) * (-(2 * (u / s) ^ 1 * (1 / s)) / 4)) u := hq.exp
  have hmul := hHe.mul hE
  unfold hermiteGauss hermiteGaussD
  convert hmul using 1
  field_simp
  ring

theorem hasDerivAt_hermiteGaussD (n : ℕ) {s : ℝ} (hs : s ≠ 0) (u : ℝ) :
    HasDerivAt (hermiteGaussD n s)
      ((u ^ 2 / (4 * s ^ 4) - ((n : ℝ) + 1 / 2) / s ^ 2) * hermiteGauss n s u) u := by
  have hv : HasDerivAt (fun t : ℝ => t / s) (1 / s) u := by
    simpa using (hasDerivAt_id u).div_const s
  have hHe : HasDerivAt (fun t : ℝ => He n (t / s)) (He' n (u / s) * (1 / s)) u := by
    simpa only [Function.comp_def] using (hasDerivAt_He n (u / s)).comp u hv
  have hHe' : HasDerivAt (fun t : ℝ => He' n (t / s)) (He'' n (u / s) * (1 / s)) u := by
    simpa only [Function.comp_def] using (hasDerivAt_He' n (u / s)).comp u hv
  have hq : HasDerivAt (fun t : ℝ => -(t / s) ^ 2 / 4) (-(2 * (u / s) ^ 1 * (1 / s)) / 4) u :=
    ((hv.pow 2).neg).div_const 4
  have hE : HasDerivAt (fun t : ℝ => Real.exp (-(t / s) ^ 2 / 4))
      (Real.exp (-(u / s) ^ 2 / 4) * (-(2 * (u / s) ^ 1 * (1 / s)) / 4)) u := hq.exp
  have h1 : HasDerivAt (fun t : ℝ => t / (2 * s ^ 2)) (1 / (2 * s ^ 2)) u := by
    simpa only [one_div] using (hasDerivAt_id u).div_const (2 * s ^ 2)
  have hlin : HasDerivAt (fun t : ℝ => t / (2 * s ^ 2) * He n (t / s))
      (1 / (2 * s ^ 2) * He n (u / s) + u / (2 * s ^ 2) * (He' n (u / s) * (1 / s))) u := h1.mul hHe
  have hfac : HasDerivAt (fun t : ℝ => He' n (t / s) / s - t / (2 * s ^ 2) * He n (t / s))
      (He'' n (u / s) * (1 / s) / s -
        (1 / (2 * s ^ 2) * He n (u / s) + u / (2 * s ^ 2) * (He' n (u / s) * (1 / s)))) u :=
    (hHe'.div_const s).sub hlin
  have hmul := hfac.mul hE
  unfold hermiteGauss hermiteGaussD
  convert hmul using 1
  rw [He_ode n (u / s)]
  field_simp
  ring

/-! ## The two-dimensional Landau problem (Landau gauge `A = (0, B x, 0)`) -/

/-- Partial derivative in the `x` variable. -/
def dx (f : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ := deriv (fun t => f t y) x

/-- Partial derivative in the `y` variable. -/
def dy (f : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ := deriv (fun t => f x t) y

/-- The `x` component of the kinematic momentum, `π_x = -i ℏ ∂_x`. -/
def piX (hbar : ℝ) (f : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ := fun x y => -Complex.I * hbar * dx f x y

/-- The `y` component of the kinematic momentum in the Landau gauge,
`π_y = -i ℏ ∂_y - q B x`. -/
def piY (hbar q B : ℝ) (f : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x y => -Complex.I * hbar * dy f x y - (q * B * x : ℝ) * f x y

/-- The Landau Hamiltonian `H = (π_x² + π_y²)/(2m)` for a particle of mass `m` and charge `q`
in the uniform magnetic field `B ẑ`, in the Landau gauge. -/
def landauH (hbar m q B : ℝ) (f : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x y => (1 / (2 * m) : ℝ) * (piX hbar (piX hbar f) x y + piY hbar q B (piY hbar q B f) x y)

/-- The magnetic length `√(ℏ/(2qB))` (the Gaussian width parameter of the Landau orbitals). -/
def magLength (hbar q B : ℝ) : ℝ := Real.sqrt (hbar / (2 * (q * B)))

/-- The guiding centre `x₀ = ℏk/(qB)` of a Landau orbital with transverse momentum `k`. -/
def guidingCenter (hbar q B k : ℝ) : ℝ := hbar * k / (q * B)

/-- The `n`-th Landau orbital with transverse momentum `k`, length scale `s`,
guiding centre `x₀`. -/
def landauPsi (n : ℕ) (s x0 k : ℝ) : ℝ → ℝ → ℂ :=
  fun x y => Complex.exp (Complex.I * k * y) * (hermiteGauss n s (x - x0) : ℝ)

/-- `x`-derivative of a function of the product form `c * e^{iky} * g(x - x₀)`. -/
theorem dx_form (f : ℝ → ℝ → ℂ) (c : ℂ) (g g' : ℝ → ℝ) (hg : ∀ t : ℝ, HasDerivAt g (g' t) t)
    (k x0 : ℝ)
    (hf : ∀ a b : ℝ, f a b = c * Complex.exp (Complex.I * k * b) * ((g (a - x0) : ℝ) : ℂ))
    (x y : ℝ) :
    dx f x y = c * Complex.exp (Complex.I * k * y) * ((g' (x - x0) : ℝ) : ℂ) := by
  have hfun : (fun t : ℝ => f t y)
      = fun t : ℝ => c * Complex.exp (Complex.I * k * y) * ((g (t - x0) : ℝ) : ℂ) := by
    funext t; exact hf t y
  have hshift : HasDerivAt (fun t : ℝ => g (t - x0)) (g' (x - x0)) x := by
    simpa using (hg (x - x0)).comp x ((hasDerivAt_id x).sub_const x0)
  have hC : HasDerivAt (fun t : ℝ => ((g (t - x0) : ℝ) : ℂ)) ((g' (x - x0) : ℝ) : ℂ) x :=
    hshift.ofReal_comp
  have hmul := hC.const_mul (c * Complex.exp (Complex.I * k * y))
  rw [dx, hfun, hmul.deriv]

/-- `y`-derivative of a function of the product form `e^{iky} * F x`. -/
theorem dy_form (f : ℝ → ℝ → ℂ) (F : ℝ → ℂ) (k : ℝ)
    (hf : ∀ a b : ℝ, f a b = Complex.exp (Complex.I * k * b) * F a) (x y : ℝ) :
    dy f x y = Complex.I * k * (Complex.exp (Complex.I * k * y) * F x) := by
  have hfun : (fun t : ℝ => f x t)
      = fun t : ℝ => Complex.exp (Complex.I * k * t) * F x := by
    funext t; exact hf x t
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => Complex.I * k * (t : ℂ)) (Complex.I * k) y := by
    simpa using h0.const_mul (Complex.I * (k : ℂ))
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * k * (t : ℂ)))
      (Complex.exp (Complex.I * k * (y : ℂ)) * (Complex.I * k)) y := h1.cexp
  have h3 := h2.mul_const (F x)
  rw [dy, hfun, h3.deriv]
  ring

/-- The algebraic identity behind the Landau spectrum: with magnetic length `s`
satisfying `s² = ℏ/(2c)` (`c = qB`) and guiding centre `x₀ = ℏk/c`, the potential terms
combine to the constant `2m · ℏ(c/m)(n + 1/2)`. -/
theorem landau_energy_algebra (hbar m c k x G nn : ℝ) (hc : c ≠ 0) (hm : m ≠ 0)
    (hhb : hbar ≠ 0) :
    -(hbar ^ 2) * (((x - hbar * k / c) ^ 2 / (4 * (hbar / (2 * c)) ^ 2)
        - (nn + 1 / 2) / (hbar / (2 * c))) * G)
      + (hbar * k - c * x) ^ 2 * G
      = 2 * m * (hbar * (c / m) * (nn + 1 / 2) * G) := by
  field_simp
  ring

/-- **Landau levels.** For a particle of mass `m > 0` and charge `q` moving in the plane in a
uniform perpendicular magnetic field `B` (with `qB > 0`), the Landau-gauge Hamiltonian
`H = ((-iℏ∂ₓ)² + (-iℏ∂_y - qBx)²)/(2m)` has the orbitals
`ψ_{n,k}(x,y) = e^{iky} He_n((x-x₀)/s) e^{-(x-x₀)²/(4s²)}` as eigenfunctions, with the
Landau-level energies `E_n = ℏ ω_c (n + 1/2)`, where `ω_c = qB/m` is the cyclotron frequency,
`s = √(ℏ/(2qB))` is the magnetic length and `x₀ = ℏk/(qB)` is the guiding centre. -/
theorem landau_levels (hbar m q B k : ℝ) (n : ℕ) (hhbar : 0 < hbar) (hm : 0 < m)
    (hqB : 0 < q * B) (x y : ℝ) :
    landauH hbar m q B (landauPsi n (magLength hbar q B) (guidingCenter hbar q B k) k) x y
      = (hbar * (q * B / m) * ((n : ℝ) + 1 / 2) : ℝ) *
          landauPsi n (magLength hbar q B) (guidingCenter hbar q B k) k x y := by
  set s : ℝ := magLength hbar q B with hs_def
  set x0 : ℝ := guidingCenter hbar q B k with hx0_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs : s ≠ 0 := ne_of_gt hs_pos
  have hs2 : s ^ 2 = hbar / (2 * (q * B)) := by
    rw [hs_def, magLength, Real.sq_sqrt (by positivity)]
  set psi : ℝ → ℝ → ℂ := landauPsi n s x0 k with hpsi_def
  have hpsi_val : ∀ a b : ℝ, psi a b
      = (1 : ℂ) * Complex.exp (Complex.I * k * b) * ((hermiteGauss n s (a - x0) : ℝ) : ℂ) := by
    intro a b; rw [hpsi_def, landauPsi]; ring
  -- the `x` direction : two derivatives of the Hermite function
  have hpiX_val : ∀ a b : ℝ, piX hbar psi a b
      = (-Complex.I * hbar) * Complex.exp (Complex.I * k * b) *
          ((hermiteGaussD n s (a - x0) : ℝ) : ℂ) := by
    intro a b
    rw [piX, dx_form psi 1 (hermiteGauss n s) (hermiteGaussD n s)
      (fun t => hasDerivAt_hermiteGauss n hs t) k x0 hpsi_val a b]
    ring
  have hpiXX : piX hbar (piX hbar psi) x y
      = (-Complex.I * hbar) * ((-Complex.I * hbar) * Complex.exp (Complex.I * k * y) *
          ((((x - x0) ^ 2 / (4 * s ^ 4) - ((n : ℝ) + 1 / 2) / s ^ 2) *
            hermiteGauss n s (x - x0) : ℝ) : ℂ)) := by
    rw [piX, dx_form (piX hbar psi) (-Complex.I * hbar) (hermiteGaussD n s)
      (fun u => (u ^ 2 / (4 * s ^ 4) - ((n : ℝ) + 1 / 2) / s ^ 2) * hermiteGauss n s u)
      (fun t => hasDerivAt_hermiteGaussD n hs t) k x0 hpiX_val x y]
  -- the `y` direction : the plane wave and the gauge potential
  have hpiY_val : ∀ a b : ℝ, piY hbar q B psi a b
      = Complex.exp (Complex.I * k * b) *
          (((hbar * k - q * B * a : ℝ) : ℂ) * ((hermiteGauss n s (a - x0) : ℝ) : ℂ)) := by
    intro a b
    have hval : ∀ c d : ℝ, psi c d
        = Complex.exp (Complex.I * k * d) * ((hermiteGauss n s (c - x0) : ℝ) : ℂ) := by
      intro c d; rw [hpsi_val c d]; ring
    rw [piY, dy_form psi (fun t : ℝ => ((hermiteGauss n s (t - x0) : ℝ) : ℂ)) k hval a b,
      hval a b]
    push_cast
    have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-(Complex.exp (Complex.I * (k : ℂ) * (b : ℂ)) *
      ((hermiteGauss n s (a - x0) : ℝ) : ℂ) * (hbar : ℂ) * (k : ℂ))) * hI2
  have hpiYY : piY hbar q B (piY hbar q B psi) x y
      = ((hbar * k - q * B * x : ℝ) : ℂ) ^ 2 *
          (Complex.exp (Complex.I * k * y) * ((hermiteGauss n s (x - x0) : ℝ) : ℂ)) := by
    rw [piY, dy_form (piY hbar q B psi)
      (fun t : ℝ => ((hbar * k - q * B * t : ℝ) : ℂ) * ((hermiteGauss n s (t - x0) : ℝ) : ℂ))
      k hpiY_val x y, hpiY_val x y]
    push_cast
    have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-(Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) *
      ((hermiteGauss n s (x - x0) : ℝ) : ℂ) * (hbar : ℂ) * (k : ℂ) *
        ((hbar : ℂ) * (k : ℂ) - (q : ℂ) * (B : ℂ) * (x : ℂ)))) * hI2
  -- combine
  have keyR : -(hbar ^ 2) * (((x - x0) ^ 2 / (4 * s ^ 4) - ((n : ℝ) + 1 / 2) / s ^ 2) *
        hermiteGauss n s (x - x0))
      + (hbar * k - q * B * x) ^ 2 * hermiteGauss n s (x - x0)
      = (2 * m) * ((hbar * (q * B / m) * ((n : ℝ) + 1 / 2)) * hermiteGauss n s (x - x0)) := by
    have hx0 : x0 = hbar * k / (q * B) := rfl
    have hs4 : s ^ 4 = (hbar / (2 * (q * B))) ^ 2 := by
      rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]
    have hqB' : (q * B) ≠ 0 := ne_of_gt hqB
    have hm' : m ≠ 0 := ne_of_gt hm
    have hhb' : hbar ≠ 0 := ne_of_gt hhbar
    rw [hx0, hs4, hs2]
    exact landau_energy_algebra hbar m (q * B) k x
      (hermiteGauss n s (x - hbar * k / (q * B))) n hqB' hm' hhb'
  have keyC : -((hbar : ℂ) ^ 2) *
      (((((x - x0) ^ 2 / (4 * s ^ 4) - ((n : ℝ) + 1 / 2) / s ^ 2) *
          hermiteGauss n s (x - x0) : ℝ)) : ℂ)
      + ((hbar * k - q * B * x : ℝ) : ℂ) ^ 2 * ((hermiteGauss n s (x - x0) : ℝ) : ℂ)
      = ((2 * m : ℝ) : ℂ) * (((hbar * (q * B / m) * ((n : ℝ) + 1 / 2) : ℝ) : ℂ) *
          ((hermiteGauss n s (x - x0) : ℝ) : ℂ)) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) keyR
    push_cast at this ⊢
    linear_combination this
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h2m : ((1 / (2 * m) : ℝ) : ℂ) * ((2 * m : ℝ) : ℂ) = 1 := by
    have hm' : m ≠ 0 := ne_of_gt hm
    have h : (1 / (2 * m) : ℝ) * (2 * m) = 1 := by field_simp
    rw [← Complex.ofReal_mul, h, Complex.ofReal_one]
  rw [landauH, hpiXX, hpiYY, hpsi_val x y]
  linear_combination (((1 / (2 * m) : ℝ) : ℂ) * Complex.exp (Complex.I * k * y)) * keyC
    + (((1 / (2 * m) : ℝ) : ℂ) * Complex.exp (Complex.I * k * y) * (hbar : ℂ) ^ 2 *
        (((((x - x0) ^ 2 / (4 * s ^ 4) - ((n : ℝ) + 1 / 2) / s ^ 2) *
            hermiteGauss n s (x - x0) : ℝ)) : ℂ)) * hI2
    + (Complex.exp (Complex.I * k * y) *
        ((hbar * (q * B / m) * ((n : ℝ) + 1 / 2) : ℝ) : ℂ) *
        ((hermiteGauss n s (x - x0) : ℝ) : ℂ)) * h2m

/-- The Landau orbitals are genuine (non-zero) eigenfunctions: `ψ_{n,k}` does not vanish
identically. -/
theorem landauPsi_ne_zero (n : ℕ) (s x0 k : ℝ) (hs : s ≠ 0) :
    ∃ x y : ℝ, landauPsi n s x0 k x y ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hHerm : Herm n ≠ 0 := ((hermite_monic n).map (Int.castRingHom ℝ)).ne_zero
  have hzero : ∀ v : ℝ, (Herm n).eval v = 0 := by
    intro v
    have h := hcon (v * s + x0) 0
    rw [landauPsi] at h
    have hexp : Complex.exp (Complex.I * (k : ℂ) * ((0 : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have h2 : ((hermiteGauss n s (v * s + x0 - x0) : ℝ) : ℂ) = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hexp
      · exact h'
    have h3 : hermiteGauss n s (v * s + x0 - x0) = 0 := by
      exact_mod_cast h2
    rw [hermiteGauss] at h3
    have h4 : He n ((v * s + x0 - x0) / s) = 0 := by
      rcases mul_eq_zero.mp h3 with h' | h'
      · exact h'
      · exact absurd h' (Real.exp_ne_zero _)
    have h5 : (v * s + x0 - x0) / s = v := by
      rw [add_sub_cancel_right]
      field_simp
    rw [h5] at h4
    exact h4
  exact hHerm (Polynomial.zero_of_eval_zero _ hzero)

end

end Frontier

