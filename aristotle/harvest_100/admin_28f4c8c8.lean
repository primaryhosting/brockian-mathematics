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

set_option grind.warning false

namespace Frontier

open Polynomial

/-! ## Physicists' Hermite polynomials -/

/-- The physicists' Hermite polynomials, defined by `H₀ = 1` and
`H_{n+1} = 2X H_n - H_n'`. -/
noncomputable def hermiteP : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => 2 * X * hermiteP n - derivative (hermiteP n)

/-- Hermite's differential equation `H_n'' - 2X H_n' + 2n H_n = 0`, together with the
derivative formula `H_{n+1}' = 2(n+1) H_n`. -/
theorem hermiteP_ode_and_derivative (n : ℕ) :
    derivative (derivative (hermiteP n)) - 2 * X * derivative (hermiteP n)
        + 2 * (n : ℝ[X]) * hermiteP n = 0 ∧
      derivative (hermiteP (n + 1)) = 2 * ((n : ℝ[X]) + 1) * hermiteP n := by
  induction n with
  | zero => refine ⟨by simp [hermiteP], by simp [hermiteP, derivative_mul]⟩
  | succ n ih =>
      obtain ⟨-, hd⟩ := ih
      have hsucc : hermiteP (n + 1) = 2 * X * hermiteP n - derivative (hermiteP n) := rfl
      have hB : derivative (derivative (hermiteP (n + 1)))
          - 2 * X * derivative (hermiteP (n + 1)) + 2 * ((n : ℝ[X]) + 1) * hermiteP (n + 1) = 0 := by
        rw [hd, hsucc]
        simp [derivative_mul, mul_sub, mul_add, add_mul]
        ring
      refine ⟨by push_cast; linear_combination hB, ?_⟩
      have hsucc2 :
          hermiteP (n + 1 + 1) = 2 * X * hermiteP (n + 1) - derivative (hermiteP (n + 1)) := rfl
      rw [hsucc2, derivative_sub, derivative_mul, derivative_mul]
      push_cast
      simp only [derivative_ofNat, derivative_X, zero_mul, mul_one, zero_add]
      linear_combination -hB

theorem hermiteP_ode (n : ℕ) :
    derivative (derivative (hermiteP n)) - 2 * X * derivative (hermiteP n)
      + 2 * (n : ℝ[X]) * hermiteP n = 0 := (hermiteP_ode_and_derivative n).1

/-- `H_n` has degree `n` with leading coefficient `2^n`. -/
theorem hermiteP_deg_coeff (n : ℕ) :
    (hermiteP n).natDegree ≤ n ∧ (hermiteP n).coeff n = 2 ^ n := by
  induction n with
  | zero => refine ⟨by simp [hermiteP], by simp [hermiteP]⟩
  | succ n ih =>
      obtain ⟨hdeg, hco⟩ := ih
      have hsucc : hermiteP (n + 1) = 2 * X * hermiteP n - derivative (hermiteP n) := rfl
      have hd1 : (2 * X * hermiteP n).natDegree ≤ n + 1 := by
        calc (2 * X * hermiteP n).natDegree
            ≤ (2 * X : ℝ[X]).natDegree + (hermiteP n).natDegree := natDegree_mul_le
          _ ≤ 1 + n := by
              gcongr
              exact le_trans natDegree_mul_le (by simp)
          _ = n + 1 := by ring
      have hd2 : (derivative (hermiteP n)).natDegree ≤ n + 1 :=
        le_trans (natDegree_derivative_le _) (by omega)
      refine ⟨le_trans (natDegree_sub_le _ _) (max_le hd1 hd2), ?_⟩
      rw [hsucc, coeff_sub, coeff_derivative]
      have h0 : (hermiteP n).coeff (n + 1 + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have h1 : (2 * X * hermiteP n).coeff (n + 1) = 2 * (hermiteP n).coeff n := by
        rw [mul_assoc, mul_comm (2 : ℝ[X]), mul_assoc]
        simp [mul_comm]
      rw [h0, h1, hco]
      ring

theorem hermiteP_ne_zero (n : ℕ) : hermiteP n ≠ 0 := by
  intro h
  have hco := (hermiteP_deg_coeff n).2
  rw [h] at hco
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  simp only [Polynomial.coeff_zero] at hco
  linarith

/-! ## Gaussian-damped polynomials and the harmonic-oscillator eigenfunctions -/

/-- `gfun p t = p(t) e^{-t²/2}`. -/
noncomputable def gfun (p : ℝ[X]) (t : ℝ) : ℝ := p.eval t * Real.exp (-t ^ 2 / 2)

theorem hasDerivAt_gfun (p : ℝ[X]) (t : ℝ) :
    HasDerivAt (gfun p) (gfun (derivative p - X * p) t) t := by
  have h1 : HasDerivAt (fun s : ℝ => p.eval s) ((derivative p).eval t) t := p.hasDerivAt t
  have h2 : HasDerivAt (fun s : ℝ => -s ^ 2 / 2) (-t) t :=
    ((hasDerivAt_pow 2 t).neg.div_const 2).congr_deriv (by push_cast; ring)
  have h3 : HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2 / 2)) (Real.exp (-t ^ 2 / 2) * (-t)) t := h2.exp
  have h4 : HasDerivAt (gfun p)
      (eval t (derivative p) * Real.exp (-t ^ 2 / 2)
        + eval t p * (Real.exp (-t ^ 2 / 2) * -t)) t := h1.mul h3
  refine h4.congr_deriv ?_
  simp [gfun]; ring

/-- Derivative of `t ↦ gfun p (c * (t - d))`. -/
theorem hasDerivAt_gfun_affine (p : ℝ[X]) (c d t : ℝ) :
    HasDerivAt (fun s : ℝ => gfun p (c * (s - d))) (c * gfun (derivative p - X * p) (c * (t - d))) t := by
  have h : HasDerivAt (fun s : ℝ => c * (s - d)) c t := by
    simpa using ((hasDerivAt_id t).sub_const d).const_mul c
  simpa [mul_comm] using (hasDerivAt_gfun p (c * (t - d))).comp t h

/-- The `n`-th harmonic oscillator eigenfunction (unnormalised): `H_n(t) e^{-t²/2}`. -/
noncomputable def oscFun (n : ℕ) : ℝ → ℝ := gfun (hermiteP n)

/-- Abbreviation for the polynomial appearing in the first derivative of `oscFun n`. -/
noncomputable def hermiteQ (n : ℕ) : Polynomial ℝ := derivative (hermiteP n) - X * hermiteP n

/-- The polynomial appearing in the second derivative of `oscFun n` is `(X² - (2n+1)) H_n`. -/
theorem hermiteQ_deriv (n : ℕ) :
    derivative (hermiteQ n) - X * hermiteQ n = (X ^ 2 - (2 * (n : ℝ[X]) + 1)) * hermiteP n := by
  have h := hermiteP_ode n
  simp only [hermiteQ, derivative_sub, derivative_mul, derivative_X, one_mul]
  linear_combination h

/-- The second derivative of the Hermite function satisfies
`u_n'' (t) = (t² - (2n+1)) u_n (t)`, i.e. `-u'' + t² u = (2n+1) u`. -/
theorem gfun_hermiteQ_deriv (n : ℕ) (s : ℝ) :
    gfun (derivative (hermiteQ n) - X * hermiteQ n) s = (s ^ 2 - (2 * n + 1)) * oscFun n s := by
  rw [hermiteQ_deriv]
  simp [gfun, oscFun]
  ring

/-- The oscillator eigenfunctions are not identically zero. -/
theorem oscFun_ne_zero (n : ℕ) : ∃ t : ℝ, oscFun n t ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  refine hermiteP_ne_zero n (Polynomial.funext fun r => ?_)
  have h := hcon r
  simp only [oscFun, gfun, mul_eq_zero] at h
  rcases h with h | h
  · simpa using h
  · exact absurd h (Real.exp_ne_zero _)

/-! ## Landau levels -/

/-- Kinetic momentum operator in the `x` direction, `π_x = -iℏ ∂_x`. -/
noncomputable def piX (hbar : ℝ) (psi : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x y => -Complex.I * hbar * deriv (fun s => psi s y) x

/-- Kinetic momentum operator in the `y` direction in the Landau gauge `A = (0, Bx, 0)`,
`π_y = -iℏ ∂_y - qBx`. -/
noncomputable def piY (hbar q B : ℝ) (psi : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x y => -Complex.I * hbar * deriv (fun s => psi x s) y - (q * B * x : ℝ) * psi x y

/-- Derivative of `y ↦ exp (i k y)`. -/
theorem hasDerivAt_cexp_lin (k y : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * k * s))
      (Complex.exp (Complex.I * k * y) * (Complex.I * k)) y := by
  have h0 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) (1 : ℂ) y := (hasDerivAt_id y).ofReal_comp
  have h1 : HasDerivAt (fun s : ℝ => Complex.I * (k : ℂ) * (s : ℂ)) (Complex.I * k) y := by
    simpa using h0.const_mul (Complex.I * (k : ℂ))
  simpa using h1.cexp

/-- On a separated state `exp (i k y) f(x)`, the operator `π_y` acts as multiplication by
`ℏk - qBx`. -/
theorem piY_sep (hbar q B k : ℝ) (f : ℝ → ℝ) :
    piY hbar q B (fun x y : ℝ => Complex.exp (Complex.I * k * y) * (f x : ℂ))
      = fun x y : ℝ =>
        Complex.exp (Complex.I * k * y) * (((hbar * k - q * B * x) * f x : ℝ) : ℂ) := by
  funext x y
  have hd : deriv (fun s : ℝ => Complex.exp (Complex.I * k * s) * (f x : ℂ)) y
      = Complex.exp (Complex.I * k * y) * (Complex.I * k) * (f x : ℂ) :=
    ((hasDerivAt_cexp_lin k y).mul_const (f x : ℂ)).deriv
  simp only [piY, hd]
  push_cast
  linear_combination (-(hbar : ℂ) * k * Complex.exp (Complex.I * k * y) * (f x : ℂ)) * Complex.I_sq

/-- On a separated state `exp (i k y) f(x)`, the operator `π_x` differentiates the `x` factor. -/
theorem piX_sep (hbar k : ℝ) (f f' : ℝ → ℝ) (h : ∀ x, HasDerivAt f (f' x) x) :
    piX hbar (fun x y : ℝ => Complex.exp (Complex.I * k * y) * (f x : ℂ))
      = fun x y : ℝ => -Complex.I * hbar * (Complex.exp (Complex.I * k * y) * (f' x : ℂ)) := by
  funext x y
  have hd : deriv (fun s : ℝ => Complex.exp (Complex.I * k * y) * (f s : ℂ)) x
      = Complex.exp (Complex.I * k * y) * (f' x : ℂ) :=
    (((h x).ofReal_comp).const_mul (Complex.exp (Complex.I * k * y))).deriv
  simp only [piX, hd]

/-- `π_x²` acts on a separated state as `-ℏ² ∂_x²`. -/
theorem piX_sq_sep (hbar k : ℝ) (f f' f'' : ℝ → ℝ) (h1 : ∀ x, HasDerivAt f (f' x) x)
    (h2 : ∀ x, HasDerivAt f' (f'' x) x) :
    piX hbar (piX hbar (fun x y : ℝ => Complex.exp (Complex.I * k * y) * (f x : ℂ)))
      = fun x y : ℝ => ((-hbar ^ 2 : ℝ) : ℂ) * (Complex.exp (Complex.I * k * y) * (f'' x : ℂ)) := by
  rw [piX_sep hbar k f f' h1]
  funext x y
  have hd : deriv (fun s : ℝ =>
      -Complex.I * hbar * (Complex.exp (Complex.I * k * y) * (f' s : ℂ))) x
      = -Complex.I * hbar * (Complex.exp (Complex.I * k * y) * (f'' x : ℂ)) :=
    ((((h2 x).ofReal_comp).const_mul (Complex.exp (Complex.I * k * y))).const_mul
      (-Complex.I * (hbar : ℂ))).deriv
  simp only [piX, hd]
  push_cast
  linear_combination ((hbar : ℂ) ^ 2 * Complex.exp (Complex.I * k * y) * (f'' x : ℂ)) * Complex.I_sq

/-- The Hamiltonian of a particle of mass `m` and charge `q` in a uniform magnetic field `B`
perpendicular to the plane, in the Landau gauge: `H = (π_x² + π_y²)/(2m)`. -/
noncomputable def landauH (m hbar q B : ℝ) (psi : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x y => (1 / (2 * m) : ℝ) *
    (piX hbar (piX hbar psi) x y + piY hbar q B (piY hbar q B psi) x y)

/-- The cyclotron frequency `ω_c = qB/m`. -/
noncomputable def omegaC (m q B : ℝ) : ℝ := q * B / m

/-- The `n`-th Landau eigenstate with transverse momentum `ℏk`, in the Landau gauge. -/
noncomputable def landauPsi (hbar q B : ℝ) (n : ℕ) (k : ℝ) : ℝ → ℝ → ℂ :=
  fun x y => Complex.exp (Complex.I * k * y) *
    (oscFun n (Real.sqrt (q * B / hbar) * (x - hbar * k / (q * B))) : ℝ)

/-- The algebraic identity behind the Landau spectrum: with `C² = Q/H` (i.e. `C = √(qB/ℏ)`),
the oscillator potential and the Gaussian curvature term combine to the constant
`H (Q/M) (N + 1/2)`. -/
theorem landau_alg (M H Q C F E N K Y : ℂ) (hM : M ≠ 0) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hC : C ^ 2 = Q / H) :
    1 / (2 * M) * (-H ^ 2 * (E * (C * (C * (((C * (Y - H * K / Q)) ^ 2 - (2 * N + 1)) * F))))
        + E * ((H * K - Q * Y) * ((H * K - Q * Y) * F)))
      = H * (Q / M) * (N + 1 / 2) * (E * F) := by
  have hQ' : Q = C ^ 2 * H := by field_simp at hC; linear_combination -hC
  have hC0 : C ≠ 0 := by
    intro h; apply hQ; rw [hQ', h]; ring
  subst hQ'
  field_simp
  ring

/-- **Landau levels.** For a charged particle of mass `m` and charge `q` moving in a plane
perpendicular to a uniform magnetic field `B`, the states `landauPsi` are eigenstates of the
Hamiltonian with energies `ℏ ω_c (n + 1/2)`, `ω_c = qB/m` the cyclotron frequency. -/
theorem landau_levels (m hbar q B k : ℝ) (n : ℕ) (hm : m ≠ 0) (hhbar : 0 < hbar)
    (hqB : 0 < q * B) :
    landauH m hbar q B (landauPsi hbar q B n k) =
      fun x y => ((hbar * omegaC m q B * (n + 1 / 2) : ℝ) : ℂ) * landauPsi hbar q B n k x y := by
  have hQ : q * B ≠ 0 := ne_of_gt hqB
  have hhb : hbar ≠ 0 := ne_of_gt hhbar
  have hc : (Real.sqrt (q * B / hbar)) ^ 2 = q * B / hbar :=
    Real.sq_sqrt (le_of_lt (div_pos hqB hhbar))
  have h1 : ∀ x : ℝ,
      HasDerivAt (fun s : ℝ => oscFun n (Real.sqrt (q * B / hbar) * (s - hbar * k / (q * B))))
        (Real.sqrt (q * B / hbar) *
          gfun (hermiteQ n) (Real.sqrt (q * B / hbar) * (x - hbar * k / (q * B)))) x :=
    fun x => hasDerivAt_gfun_affine (hermiteP n) _ _ x
  have h2 : ∀ x : ℝ,
      HasDerivAt (fun s : ℝ => Real.sqrt (q * B / hbar) *
          gfun (hermiteQ n) (Real.sqrt (q * B / hbar) * (s - hbar * k / (q * B))))
        (Real.sqrt (q * B / hbar) * (Real.sqrt (q * B / hbar) *
          gfun (derivative (hermiteQ n) - X * hermiteQ n)
            (Real.sqrt (q * B / hbar) * (x - hbar * k / (q * B))))) x :=
    fun x => (hasDerivAt_gfun_affine (hermiteQ n) _ _ x).const_mul _
  have hpsi : landauPsi hbar q B n k = fun x y : ℝ => Complex.exp (Complex.I * k * y) *
      (((fun s : ℝ => oscFun n (Real.sqrt (q * B / hbar) * (s - hbar * k / (q * B)))) x : ℝ) : ℂ) :=
    rfl
  funext x y
  rw [hpsi]
  simp only [landauH, piX_sq_sep hbar k _ _ _ h1 h2, piY_sep]
  rw [gfun_hermiteQ_deriv]
  simp only [omegaC]
  push_cast
  have hCsq : ((Real.sqrt (q * B / hbar) : ℝ) : ℂ) ^ 2 = ((q : ℂ) * B) / (hbar : ℂ) := by
    rw [← Complex.ofReal_pow, hc]; push_cast; ring
  have halg := landau_alg (m : ℂ) (hbar : ℂ) ((q : ℂ) * B)
    ((Real.sqrt (q * B / hbar) : ℝ) : ℂ)
    ((oscFun n (Real.sqrt (q * B / hbar) * (x - hbar * k / (q * B))) : ℝ) : ℂ)
    (Complex.exp (Complex.I * k * y)) (n : ℂ) (k : ℂ) (x : ℂ)
    (by exact_mod_cast hm) (by exact_mod_cast hhb) (by exact_mod_cast hQ) hCsq
  linear_combination halg

/-- The Landau eigenstates are genuinely nonzero, so `landau_levels` really exhibits
`ℏ ω_c (n + 1/2)` as an eigenvalue. -/
theorem landauPsi_ne_zero (hbar q B k : ℝ) (n : ℕ) (hhbar : 0 < hbar) (hqB : 0 < q * B) :
    landauPsi hbar q B n k ≠ 0 := by
  obtain ⟨t, ht⟩ := oscFun_ne_zero n
  have hcpos : 0 < Real.sqrt (q * B / hbar) := Real.sqrt_pos.mpr (div_pos hqB hhbar)
  have hc0 : Real.sqrt (q * B / hbar) ≠ 0 := ne_of_gt hcpos
  intro h
  have h0 : landauPsi hbar q B n k
      (t / Real.sqrt (q * B / hbar) + hbar * k / (q * B)) 0 = 0 := by rw [h]; rfl
  rw [landauPsi] at h0
  have harg : Real.sqrt (q * B / hbar) *
      (t / Real.sqrt (q * B / hbar) + hbar * k / (q * B) - hbar * k / (q * B)) = t := by
    field_simp
    ring
  rw [harg] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Complex.exp_ne_zero _ h1
  · exact ht (by exact_mod_cast h1)

end Frontier

