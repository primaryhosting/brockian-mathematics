/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is a plain block
-- comment; the same text is repeated below as the module docstring.)

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

/-! ### Hermite polynomials: the Hermite differential equation

Mathlib provides `Polynomial.hermite : ℕ → ℤ[X]` (the *probabilists'* Hermite polynomials)
together with `Polynomial.hermite_succ`, but not the Hermite ODE, which we derive here. -/

/-- The Hermite differential equation `He_n'' = X * He_n' - n * He_n`. -/
theorem hermite_ode (n : ℕ) :
    derivative (derivative (hermite n)) = X * derivative (hermite n) - (n : ℤ[X]) * hermite n := by
  induction n with
  | zero => simp [hermite_zero]
  | succ n ih =>
      have hd : derivative (hermite (n + 1)) = ((n : ℤ[X]) + 1) * hermite n := by
        rw [hermite_succ n]
        simp only [derivative_sub, derivative_mul, derivative_X, one_mul]
        rw [ih]; ring
      rw [hd, hermite_succ n]
      simp only [derivative_mul, derivative_natCast, derivative_one, derivative_add]
      push_cast
      ring_nf

/-- The `n`-th (probabilists') Hermite polynomial with real coefficients. -/
noncomputable def hermiteR (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

theorem hermiteR_eval (n : ℕ) (x : ℝ) : (hermiteR n).eval x = Polynomial.aeval x (hermite n) := by
  rw [hermiteR, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]; rfl

theorem hermiteR_ode (n : ℕ) :
    derivative (derivative (hermiteR n)) = X * derivative (hermiteR n) - C (n : ℝ) * hermiteR n := by
  unfold hermiteR
  rw [derivative_map, derivative_map, hermite_ode n]
  simp [Polynomial.map_sub, Polynomial.map_mul]

/-! ### Polynomial times Gaussian: derivatives -/

/-- A polynomial in `a * (s - x₀)` multiplied by the Gaussian `exp (-(b * (s - x₀)^2))`. -/
noncomputable def polyGauss (q : ℝ[X]) (a b x0 : ℝ) : ℝ → ℝ :=
  fun s => q.eval (a * (s - x0)) * Real.exp (-(b * (s - x0) ^ 2))

theorem hasDerivAt_polyGauss (q : ℝ[X]) (a b x0 t : ℝ) :
    HasDerivAt (polyGauss q a b x0)
      ((a * (derivative q).eval (a * (t - x0)) - 2 * b * (t - x0) * q.eval (a * (t - x0)))
        * Real.exp (-(b * (t - x0) ^ 2))) t := by
  have h1 : HasDerivAt (fun s : ℝ => a * (s - x0)) a t := by
    simpa using ((hasDerivAt_id t).sub_const x0).const_mul a
  have h2 : HasDerivAt (fun s : ℝ => q.eval (a * (s - x0)))
      ((derivative q).eval (a * (t - x0)) * a) t := by
    simpa [Function.comp_def] using HasDerivAt.comp t (q.hasDerivAt (a * (t - x0))) h1
  have h3 : HasDerivAt (fun s : ℝ => -(b * (s - x0) ^ 2)) (-(b * (2 * (t - x0)))) t := by
    have := (((hasDerivAt_id t).sub_const x0).pow 2).const_mul b
    simpa using this.neg
  have h5 := h2.mul h3.exp
  unfold polyGauss
  convert h5 using 1
  ring

theorem differentiable_polyGauss (q : ℝ[X]) (a b x0 : ℝ) :
    Differentiable ℝ (polyGauss q a b x0) :=
  fun t => (hasDerivAt_polyGauss q a b x0 t).differentiableAt

/-- The derivative of a polynomial-times-Gaussian is again of the same shape. -/
theorem deriv_polyGauss (q : ℝ[X]) (a b x0 : ℝ) (ha : a ≠ 0) :
    deriv (polyGauss q a b x0)
      = polyGauss (C a * derivative q - C (2 * b / a) * (X * q)) a b x0 := by
  funext t
  rw [(hasDerivAt_polyGauss q a b x0 t).deriv]
  simp only [polyGauss, eval_sub, eval_mul, eval_C, eval_X]
  field_simp

/-- Second derivative of `He`-type solutions: if `q'' = X q' - c q` and `a² = 4b`, then
`(q(a(x-x₀)) e^{-b(x-x₀)²})'' = (4b²(x-x₀)² - 2b(2c+1)) q(a(x-x₀)) e^{-b(x-x₀)²}`. -/
theorem polyGauss_second_deriv (q : ℝ[X]) (c a b x0 : ℝ) (ha : a ≠ 0) (hab : a ^ 2 = 4 * b)
    (hq : derivative (derivative q) = X * derivative q - C c * q) (x : ℝ) :
    deriv (deriv (polyGauss q a b x0)) x
      = (4 * b ^ 2 * (x - x0) ^ 2 - 2 * b * (2 * c + 1)) * polyGauss q a b x0 x := by
  rw [deriv_polyGauss q a b x0 ha]
  set R : ℝ[X] := C a * derivative q - C (2 * b / a) * (X * q) with hR
  rw [(hasDerivAt_polyGauss R a b x0 x).deriv]
  have hev : (derivative (derivative q)).eval (a * (x - x0))
      = (a * (x - x0)) * (derivative q).eval (a * (x - x0)) - c * q.eval (a * (x - x0)) := by
    rw [hq]; simp
  have hdR : derivative R
      = C a * derivative (derivative q) - C (2 * b / a) * (q + X * derivative q) := by
    simp [hR, derivative_mul]
  rw [hdR]
  simp only [polyGauss, eval_sub, eval_add, eval_mul, eval_C, eval_X, hR]
  rw [hev]
  have hb : b = a ^ 2 / 4 := by linarith
  subst hb
  field_simp
  ring

/-! ### The one-dimensional harmonic oscillator -/

/-- The oscillator eigenfunction written in the normalized `polyGauss` shape. -/
theorem psi_eq_polyGauss (hbar m om x0 : ℝ) (hh : 0 < hbar) (hm : 0 < m) (ho : 0 < om)
    (n : ℕ) (ell : ℝ) (hell : ell = Real.sqrt (hbar / (m * om)))
    (psi : ℝ → ℝ)
    (hpsi : ∀ x, psi x = Polynomial.aeval (Real.sqrt 2 * (x - x0) / ell) (hermite n)
      * Real.exp (-((x - x0) ^ 2 / (2 * ell ^ 2)))) :
    ∃ a b : ℝ, a ≠ 0 ∧ a ^ 2 = 4 * b ∧ b = m * om / (2 * hbar) ∧
      psi = polyGauss (hermiteR n) a b x0 := by
  have hpos : 0 < hbar / (m * om) := by positivity
  have hell0 : 0 < ell := by rw [hell]; exact Real.sqrt_pos.mpr hpos
  have hell2 : ell ^ 2 = hbar / (m * om) := by rw [hell, Real.sq_sqrt hpos.le]
  refine ⟨Real.sqrt 2 / ell, 1 / (2 * ell ^ 2), ?_, ?_, ?_, ?_⟩
  · have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    positivity
  · rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
    norm_num
  · rw [hell2]; field_simp
  · funext s
    rw [hpsi s]
    simp only [polyGauss]
    rw [hermiteR_eval,
      show Real.sqrt 2 / ell * (s - x0) = Real.sqrt 2 * (s - x0) / ell from by ring,
      show 1 / (2 * ell ^ 2) * (s - x0) ^ 2 = (s - x0) ^ 2 / (2 * ell ^ 2) from by ring]

/-- **Harmonic oscillator spectrum.**  With `ℓ = √(ħ/(mω))` the oscillator length, the
function `ψ_n(x) = He_n(√2 (x-x₀)/ℓ) exp(-(x-x₀)²/(2ℓ²))` is an eigenfunction of the
Hamiltonian `-ħ²/(2m) d²/dx² + ½ m ω² (x-x₀)²` with eigenvalue `ħω(n + ½)`. -/
theorem harmonic_oscillator_levels (hbar m om x0 : ℝ) (hh : 0 < hbar) (hm : 0 < m) (ho : 0 < om)
    (n : ℕ) (ell : ℝ) (hell : ell = Real.sqrt (hbar / (m * om)))
    (psi : ℝ → ℝ)
    (hpsi : ∀ x, psi x = Polynomial.aeval (Real.sqrt 2 * (x - x0) / ell) (hermite n)
      * Real.exp (-((x - x0) ^ 2 / (2 * ell ^ 2)))) (x : ℝ) :
    -(hbar ^ 2 / (2 * m)) * deriv (deriv psi) x + (1 / 2) * m * om ^ 2 * (x - x0) ^ 2 * psi x
      = hbar * om * (n + 1 / 2) * psi x := by
  have hb := psi_eq_polyGauss hbar m om x0 hh hm ho n ell hell psi hpsi
  obtain ⟨a, b, ha, hab, hbval, hfun⟩ := hb
  rw [hfun, polyGauss_second_deriv (hermiteR n) (n : ℝ) a b x0 ha hab (hermiteR_ode n) x, hbval]
  have hne : hbar ≠ 0 := ne_of_gt hh
  have hmne : m ≠ 0 := ne_of_gt hm
  field_simp
  ring

/-! ### Landau levels: a charged particle in a uniform magnetic field -/

/-- **Landau levels.**  A particle of mass `m` and charge `q > 0` in a uniform magnetic field
`B ẑ`, described in the Landau gauge `A = (0, B x, 0)`, has Hamiltonian
`H = (π_x² + π_y²)/(2m)` with kinetic momenta `π_x = -iħ ∂_x` and `π_y = -iħ ∂_y - q B x`.
For every `n : ℕ` and every transverse wavenumber `k`, the state
`Ψ(x,y) = e^{i k y} · He_n(√2 (x-x₀)/ℓ) · e^{-(x-x₀)²/(2ℓ²)}`,
with guiding centre `x₀ = ħk/(qB)` and magnetic length `ℓ = √(ħ/(m ω_c))`,
is an eigenstate of `H` with energy `ħ ω_c (n + ½)`, where `ω_c = qB/m` is the cyclotron
frequency.  Thus the energy spectrum consists of the Landau levels `ħ ω_c (n + ½)`. -/
theorem landau_levels
    (hbar m charge B k : ℝ) (hh : 0 < hbar) (hm : 0 < m) (hcharge : 0 < charge) (hB : 0 < B)
    (n : ℕ)
    (omc : ℝ) (homc : omc = charge * B / m)
    (x0 : ℝ) (hx0 : x0 = hbar * k / (charge * B))
    (ell : ℝ) (hell : ell = Real.sqrt (hbar / (m * omc)))
    (psi : ℝ → ℝ)
    (hpsi : ∀ x, psi x = Polynomial.aeval (Real.sqrt 2 * (x - x0) / ell) (hermite n)
      * Real.exp (-((x - x0) ^ 2 / (2 * ell ^ 2))))
    (Psi : ℝ → ℝ → ℂ)
    (hPsi : ∀ x y, Psi x y = Complex.exp (Complex.I * k * y) * (psi x : ℂ))
    (pix piy : (ℝ → ℝ → ℂ) → ℝ → ℝ → ℂ)
    (hpix : ∀ F x y, pix F x y = -Complex.I * (hbar : ℂ) * deriv (fun s : ℝ => F s y) x)
    (hpiy : ∀ F x y, piy F x y
      = -Complex.I * (hbar : ℂ) * deriv (fun t : ℝ => F x t) y - ((charge * B * x : ℝ) : ℂ) * F x y)
    (x y : ℝ) :
    (1 / (2 * (m : ℂ))) * (pix (pix Psi) x y + piy (piy Psi) x y)
      = ((hbar * omc * (n + 1 / 2) : ℝ) : ℂ) * Psi x y := by
  have hmne : m ≠ 0 := ne_of_gt hm
  have hmne' : (m : ℂ) ≠ 0 := by exact_mod_cast hmne
  have homc0 : 0 < omc := by rw [homc]; positivity
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  -- derivative of the plane-wave factor in the `y` direction
  have hE : ∀ v : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * k * t))
      (Complex.I * k * Complex.exp (Complex.I * k * v)) v := by
    intro v
    have h0 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 v := (hasDerivAt_id v).ofReal_comp
    have h1 : HasDerivAt (fun t : ℝ => Complex.I * k * (t : ℂ)) (Complex.I * k) v := by
      simpa using h0.const_mul (Complex.I * (k : ℂ))
    simpa [mul_comm] using h1.cexp
  -- smoothness of the transverse profile
  obtain ⟨a, b, ha, hab, hbval, hfun⟩ :=
    psi_eq_polyGauss hbar m omc x0 hh hm homc0 n ell hell psi hpsi
  have hdiff : Differentiable ℝ psi := by rw [hfun]; exact differentiable_polyGauss _ _ _ _
  have hdiff2 : Differentiable ℝ (deriv psi) := by
    rw [hfun, deriv_polyGauss _ _ _ _ ha]; exact differentiable_polyGauss _ _ _ _
  -- first application of `π_x`
  have hpixPsi : ∀ u v : ℝ, pix Psi u v
      = (-Complex.I * (hbar : ℂ) * Complex.exp (Complex.I * k * v)) * ((deriv psi u : ℝ) : ℂ) := by
    intro u v
    rw [hpix]
    have hfe : (fun s : ℝ => Psi s v)
        = fun s : ℝ => Complex.exp (Complex.I * k * v) * ((psi s : ℝ) : ℂ) := by
      funext s; exact hPsi s v
    rw [hfe, (((hdiff u).hasDerivAt.ofReal_comp).const_mul _).deriv]
    ring
  -- second application of `π_x`
  have hpix2 : pix (pix Psi) x y
      = (-(hbar : ℂ) ^ 2 * Complex.exp (Complex.I * k * y)) * ((deriv (deriv psi) x : ℝ) : ℂ) := by
    rw [hpix]
    have hfe : (fun s : ℝ => pix Psi s y)
        = fun s : ℝ => (-Complex.I * (hbar : ℂ) * Complex.exp (Complex.I * k * y))
            * ((deriv psi s : ℝ) : ℂ) := by
      funext s; exact hpixPsi s y
    rw [hfe, (((hdiff2 x).hasDerivAt.ofReal_comp).const_mul _).deriv]
    linear_combination ((hbar : ℂ) ^ 2 * Complex.exp (Complex.I * k * y)
      * ((deriv (deriv psi) x : ℝ) : ℂ)) * hI
  -- first application of `π_y`
  have hpiyPsi : ∀ u v : ℝ, piy Psi u v = ((hbar * k - charge * B * u : ℝ) : ℂ) * Psi u v := by
    intro u v
    rw [hpiy]
    have hfe : (fun t : ℝ => Psi u t)
        = fun t : ℝ => ((psi u : ℝ) : ℂ) * Complex.exp (Complex.I * k * t) := by
      funext t; rw [hPsi u t]; ring
    rw [hfe, ((hE v).const_mul ((psi u : ℝ) : ℂ)).deriv, hPsi u v]
    push_cast
    linear_combination (-(hbar : ℂ) * (k : ℂ) * ((psi u : ℝ) : ℂ)
      * Complex.exp (Complex.I * k * v)) * hI
  -- second application of `π_y`
  have hpiy2 : piy (piy Psi) x y = ((hbar * k - charge * B * x : ℝ) : ℂ) ^ 2 * Psi x y := by
    rw [hpiy]
    have hfe : (fun t : ℝ => piy Psi x t)
        = fun t : ℝ => (((hbar * k - charge * B * x : ℝ) : ℂ) * ((psi x : ℝ) : ℂ))
            * Complex.exp (Complex.I * k * t) := by
      funext t; rw [hpiyPsi x t, hPsi x t]; ring
    rw [hfe, ((hE y).const_mul _).deriv, hpiyPsi x y, hPsi x y]
    push_cast
    linear_combination (-(hbar : ℂ) * (k : ℂ)
      * ((hbar : ℂ) * (k : ℂ) - (charge : ℂ) * (B : ℂ) * (x : ℂ)) * ((psi x : ℝ) : ℂ)
      * Complex.exp (Complex.I * k * y)) * hI
  -- the magnetic potential is the oscillator potential about the guiding centre
  have hcb : (charge : ℂ) * (B : ℂ) = (m : ℂ) * (omc : ℂ) := by
    rw [homc]; push_cast; field_simp
  have hhk : (hbar : ℂ) * (k : ℂ) = (charge : ℂ) * (B : ℂ) * (x0 : ℂ) := by
    have hcne : ((charge : ℂ) * (B : ℂ)) ≠ 0 := by
      rw [hcb]
      have homcne : (omc : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt homc0
      exact mul_ne_zero hmne' homcne
    rw [hx0]; push_cast
    exact Eq.symm (mul_div_cancel₀ ((hbar : ℂ) * (k : ℂ)) hcne)
  have hpot : ((hbar * k - charge * B * x : ℝ) : ℂ) ^ 2
      = 2 * (m : ℂ) * ((1 / 2) * (m : ℂ) * (omc : ℂ) ^ 2 * ((x : ℂ) - (x0 : ℂ)) ^ 2) := by
    have h1 : ((hbar : ℂ) * (k : ℂ) - (charge : ℂ) * (B : ℂ) * (x : ℂ)) ^ 2
        = ((m : ℂ) * (omc : ℂ)) ^ 2 * ((x : ℂ) - (x0 : ℂ)) ^ 2 := by
      linear_combination ((hbar : ℂ) * (k : ℂ) + (charge : ℂ) * (B : ℂ) * (x0 : ℂ)
          - 2 * (charge : ℂ) * (B : ℂ) * (x : ℂ)) * hhk
        + (((charge : ℂ) * (B : ℂ) + (m : ℂ) * (omc : ℂ)) * ((x : ℂ) - (x0 : ℂ)) ^ 2) * hcb
    push_cast
    rw [h1]
    ring
  -- the one-dimensional eigenvalue equation
  have hreal := harmonic_oscillator_levels hbar m omc x0 hh hm homc0 n ell hell psi hpsi x
  field_simp at hreal
  have hkey := Complex.ofReal_inj.mpr hreal
  push_cast at hkey
  rw [hpix2, hpiy2, hPsi x y, hpot]
  push_cast
  field_simp
  linear_combination hkey

/-! ### An explicit instance of the Landau eigenvalue equation

The hypotheses of `Frontier.landau_levels` are all definitional: they merely name the
cyclotron frequency, the guiding centre, the magnetic length, the eigenstate and the two
kinetic-momentum operators.  The following corollary instantiates them, exhibiting a concrete
eigenstate for each Landau level `n` and so showing the statement above is not vacuous. -/

/-- Cyclotron frequency `ω_c = qB/m`. -/
noncomputable def cyclotronFreq (charge B m : ℝ) : ℝ := charge * B / m

/-- Guiding centre `x₀ = ħk/(qB)` of a Landau-gauge eigenstate with wavenumber `k`. -/
noncomputable def guidingCentre (hbar charge B k : ℝ) : ℝ := hbar * k / (charge * B)

/-- Magnetic length `ℓ = √(ħ/(m ω_c))`. -/
noncomputable def magneticLength (hbar m omc : ℝ) : ℝ := Real.sqrt (hbar / (m * omc))

/-- The transverse profile of the `n`-th Landau eigenstate. -/
noncomputable def landauProfile (hbar m charge B k : ℝ) (n : ℕ) : ℝ → ℝ := fun x =>
  Polynomial.aeval (Real.sqrt 2 * (x - guidingCentre hbar charge B k)
      / magneticLength hbar m (cyclotronFreq charge B m)) (hermite n)
    * Real.exp (-((x - guidingCentre hbar charge B k) ^ 2
        / (2 * magneticLength hbar m (cyclotronFreq charge B m) ^ 2)))

/-- The `n`-th Landau eigenstate with transverse wavenumber `k`, in the Landau gauge. -/
noncomputable def landauState (hbar m charge B k : ℝ) (n : ℕ) : ℝ → ℝ → ℂ := fun x y =>
  Complex.exp (Complex.I * k * y) * ((landauProfile hbar m charge B k n x : ℝ) : ℂ)

/-- The kinetic momentum `π_x = -iħ ∂_x`. -/
noncomputable def kineticPx (hbar : ℝ) (F : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ := fun x y =>
  -Complex.I * (hbar : ℂ) * deriv (fun s : ℝ => F s y) x

/-- The kinetic momentum `π_y = -iħ ∂_y - q B x` in the Landau gauge `A = (0, Bx, 0)`. -/
noncomputable def kineticPy (hbar charge B : ℝ) (F : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ := fun x y =>
  -Complex.I * (hbar : ℂ) * deriv (fun t : ℝ => F x t) y - ((charge * B * x : ℝ) : ℂ) * F x y

/-- **Landau levels, explicit form.**  For all `n`, `k`, the state `landauState` satisfies
`H Ψ = ħ ω_c (n + ½) Ψ` for the Landau Hamiltonian `H = (π_x² + π_y²)/(2m)`. -/
theorem landau_levels_explicit (hbar m charge B k : ℝ) (hh : 0 < hbar) (hm : 0 < m)
    (hcharge : 0 < charge) (hB : 0 < B) (n : ℕ) (x y : ℝ) :
    (1 / (2 * (m : ℂ)))
        * (kineticPx hbar (kineticPx hbar (landauState hbar m charge B k n)) x y
          + kineticPy hbar charge B
              (kineticPy hbar charge B (landauState hbar m charge B k n)) x y)
      = ((hbar * cyclotronFreq charge B m * (n + 1 / 2) : ℝ) : ℂ)
          * landauState hbar m charge B k n x y :=
  landau_levels hbar m charge B k hh hm hcharge hB n _ rfl _ rfl _ rfl
    (landauProfile hbar m charge B k n) (fun _ => rfl)
    (landauState hbar m charge B k n) (fun _ _ => rfl)
    (kineticPx hbar) (kineticPy hbar charge B) (fun _ _ _ => rfl) (fun _ _ _ => rfl) x y

end Frontier

