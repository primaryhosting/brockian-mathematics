/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial

namespace QPhys

/-! ## Hermite polynomials over `ℝ`

We reuse Mathlib's (probabilists') Hermite polynomials `Polynomial.hermite : ℕ → ℤ[X]`
(`Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`), pushed forward to `ℝ[X]`.
-/

/-- The `n`-th (probabilists') Hermite polynomial, with real coefficients. -/
noncomputable def Hr (n : ℕ) : Polynomial ℝ := (Polynomial.hermite n).map (Int.castRingHom ℝ)

lemma Hr_zero : Hr 0 = 1 := by simp [Hr, Polynomial.hermite_zero]

lemma Hr_one : Hr 1 = X := by simp [Hr]

/-- The defining recursion `Heₙ₊₁ = X Heₙ - Heₙ'`. -/
lemma Hr_succ (n : ℕ) : Hr (n + 1) = X * Hr n - derivative (Hr n) := by
  simp [Hr, Polynomial.hermite_succ, Polynomial.derivative_map]

/-- `Heₙ₊₁' = (n+1) Heₙ`. -/
lemma Hr_deriv_succ (n : ℕ) : derivative (Hr (n + 1)) = ((n : Polynomial ℝ) + 1) * Hr n := by
  induction n with
  | zero => simp [Hr_one, Hr_zero]
  | succ n ih =>
      rw [Hr_succ (n + 1), derivative_sub, derivative_mul, ih]
      simp only [derivative_X, one_mul, derivative_mul, derivative_add, derivative_natCast,
        derivative_one, zero_add, add_zero, zero_mul]
      rw [Hr_succ n]
      push_cast
      ring

/-- The Hermite differential equation `Heₙ'' = X Heₙ' - n Heₙ`. -/
lemma Hr_ode (n : ℕ) :
    derivative (derivative (Hr n)) = X * derivative (Hr n) - (n : Polynomial ℝ) * Hr n := by
  cases n with
  | zero => simp [Hr_zero]
  | succ n =>
      rw [Hr_deriv_succ n]
      simp only [derivative_mul, derivative_add, derivative_natCast, derivative_one, zero_add,
        zero_mul]
      rw [Hr_succ n]
      push_cast
      ring

lemma Hr_ne_zero (n : ℕ) : Hr n ≠ 0 :=
  ((Polynomial.hermite_monic n).map (Int.castRingHom ℝ)).ne_zero

/-! ## The dimensionless oscillator -/

/-- The polynomial part of `(y/2 - d/dy)` acting on `p(y) e^{-y²/4}` (up to sign):
if `f(y) = p(y) e^{-y²/4}` then `f'(y) = (Dop p)(y) e^{-y²/4}`. -/
noncomputable def Dop (p : Polynomial ℝ) : Polynomial ℝ := derivative p - C (1 / 2) * X * p

/-- The `n`-th (unnormalised) oscillator eigenfunction in dimensionless variables. -/
noncomputable def psi (n : ℕ) (y : ℝ) : ℝ := (Hr n).eval y * Real.exp (-(y ^ 2 / 4))

lemma hasDerivAt_polyGauss (p : Polynomial ℝ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => p.eval t * Real.exp (-(t ^ 2 / 4)))
      ((Dop p).eval y * Real.exp (-(y ^ 2 / 4))) y := by
  have h1 : HasDerivAt (fun t : ℝ => p.eval t) ((derivative p).eval y) y := p.hasDerivAt y
  have h2 : HasDerivAt (fun t : ℝ => -(t ^ 2 / 4)) (-(y / 2)) y := by
    have : HasDerivAt (fun t : ℝ => t ^ 2 / 4) (y / 2) y := by
      have := (hasDerivAt_pow 2 y).div_const 4
      simpa using this.congr_deriv (by ring)
    simpa using this.neg
  refine (h1.mul h2.exp).congr_deriv ?_
  simp [Dop]
  ring

lemma hasDerivAt_psi (n : ℕ) (y : ℝ) :
    HasDerivAt (psi n) ((Dop (Hr n)).eval y * Real.exp (-(y ^ 2 / 4))) y :=
  hasDerivAt_polyGauss (Hr n) y

lemma deriv_psi (n : ℕ) :
    deriv (psi n) = fun y => (Dop (Hr n)).eval y * Real.exp (-(y ^ 2 / 4)) :=
  funext fun y => (hasDerivAt_psi n y).deriv

lemma hasDerivAt_deriv_psi (n : ℕ) (y : ℝ) :
    HasDerivAt (deriv (psi n)) ((Dop (Dop (Hr n))).eval y * Real.exp (-(y ^ 2 / 4))) y := by
  rw [deriv_psi n]
  exact hasDerivAt_polyGauss (Dop (Hr n)) y

lemma deriv_deriv_psi (n : ℕ) :
    deriv (deriv (psi n)) = fun y => (Dop (Dop (Hr n))).eval y * Real.exp (-(y ^ 2 / 4)) :=
  funext fun y => (hasDerivAt_deriv_psi n y).deriv

/-! ### Ladder operators -/

/-- The annihilation (lowering) operator `a = y/2 + d/dy` in dimensionless variables. -/
noncomputable def annihilation (f : ℝ → ℝ) : ℝ → ℝ := fun y => (y / 2) * f y + deriv f y

/-- The creation (raising) operator `a† = y/2 - d/dy` in dimensionless variables. -/
noncomputable def creation (f : ℝ → ℝ) : ℝ → ℝ := fun y => (y / 2) * f y - deriv f y

/-- `a†` raises: `a† ψₙ = ψₙ₊₁`. -/
lemma creation_psi (n : ℕ) : creation (psi n) = psi (n + 1) := by
  funext y
  simp only [creation, psi, deriv_psi n, Dop, Hr_succ n]
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  ring

/-- `a` lowers: `a ψₙ₊₁ = (n+1) ψₙ`. -/
lemma annihilation_psi_succ (n : ℕ) :
    annihilation (psi (n + 1)) = fun y => ((n : ℝ) + 1) * psi n y := by
  funext y
  simp only [annihilation, psi, deriv_psi (n + 1), Dop, Hr_deriv_succ n]
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_natCast]
  ring

/-- `a ψ₀ = 0`: the ground state is annihilated by the lowering operator. -/
lemma annihilation_psi_zero : annihilation (psi 0) = 0 := by
  funext y
  simp only [annihilation, psi, deriv_psi 0, Dop, Hr_zero]
  simp only [derivative_one, eval_sub, eval_mul, eval_C, eval_X, eval_one, zero_sub]
  simp
  ring

/-- The number operator `N = a† a` has eigenvalue `n` on `ψₙ`. -/
lemma number_operator_psi (n : ℕ) :
    creation (annihilation (psi n)) = fun y => (n : ℝ) * psi n y := by
  cases n with
  | zero =>
      rw [annihilation_psi_zero]
      funext y
      simp [creation]
  | succ n =>
      rw [annihilation_psi_succ n]
      funext y
      have hderiv : deriv (fun y => ((n : ℝ) + 1) * psi n y) y = ((n : ℝ) + 1) * deriv (psi n) y :=
        deriv_const_mul _ (hasDerivAt_psi n y).differentiableAt
      have := congrFun (creation_psi n) y
      simp only [creation, hderiv] at this ⊢
      push_cast
      nlinarith [this]

/-- The key polynomial identity behind the eigenvalue equation. -/
lemma Dop_Dop_Hr (n : ℕ) :
    -Dop (Dop (Hr n)) + C (1 / 4) * X ^ 2 * Hr n = ((n : Polynomial ℝ) + C (1 / 2)) * Hr n := by
  simp only [Dop, derivative_sub, derivative_mul, derivative_X, derivative_C, mul_one,
    zero_mul, zero_add]
  rw [Hr_ode n]
  apply Polynomial.funext
  intro y
  simp only [eval_add, eval_sub, eval_mul, eval_neg, eval_X, eval_C, eval_pow, eval_natCast]
  ring

/-- Dimensionless eigenvalue equation: `-ψₙ'' + (y²/4) ψₙ = (n + 1/2) ψₙ`. -/
lemma psi_eigen (n : ℕ) (y : ℝ) :
    -deriv (deriv (psi n)) y + (y ^ 2 / 4) * psi n y = ((n : ℝ) + 1 / 2) * psi n y := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval y) (Dop_Dop_Hr n)
  simp only [eval_add, eval_mul, eval_neg, eval_C, eval_pow, eval_X, eval_natCast] at h
  rw [deriv_deriv_psi n]
  simp only [psi]
  nlinarith [h, Real.exp_pos (-(y ^ 2 / 4))]

lemma psi_ne_zero (n : ℕ) : ∃ y : ℝ, psi n y ≠ 0 := by
  by_contra h
  push_neg at h
  refine Hr_ne_zero n (Polynomial.funext fun y => ?_)
  have := h y
  simp only [psi, mul_eq_zero] at this
  rcases this with h1 | h2
  · simpa using h1
  · exact absurd h2 (Real.exp_ne_zero _)

/-! ## The physical oscillator -/

/-- The characteristic inverse length `c = √(2mω/ℏ)`. -/
noncomputable def scale (hbar m omega : ℝ) : ℝ := Real.sqrt (2 * m * omega / hbar)

/-- The `n`-th (unnormalised) energy eigenfunction of the harmonic oscillator
`H = -(ℏ²/2m) d²/dx² + (1/2) m ω² x²`, obtained from the ground state by the ladder operators. -/
noncomputable def oscWave (hbar m omega : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  psi n (scale hbar m omega * x)

/-- `f` is an eigenfunction of the harmonic oscillator Hamiltonian with energy `E`. -/
def IsOscEigenstate (hbar m omega E : ℝ) (f : ℝ → ℝ) : Prop :=
  f ≠ 0 ∧ ∃ f' f'' : ℝ → ℝ, (∀ x, HasDerivAt f (f' x) x) ∧ (∀ x, HasDerivAt f' (f'' x) x) ∧
    ∀ x, -(hbar ^ 2 / (2 * m)) * f'' x + (1 / 2) * m * omega ^ 2 * x ^ 2 * f x = E * f x

lemma scale_pos {hbar m omega : ℝ} (hh : 0 < hbar) (hm : 0 < m) (ho : 0 < omega) :
    0 < scale hbar m omega :=
  Real.sqrt_pos.2 (by positivity)

lemma scale_sq {hbar m omega : ℝ} (hh : 0 < hbar) (hm : 0 < m) (ho : 0 < omega) :
    scale hbar m omega ^ 2 = 2 * m * omega / hbar :=
  Real.sq_sqrt (by positivity)

lemma oscWave_ne_zero {hbar m omega : ℝ} (hh : 0 < hbar) (hm : 0 < m) (ho : 0 < omega) (n : ℕ) :
    oscWave hbar m omega n ≠ 0 := by
  obtain ⟨y, hy⟩ := psi_ne_zero n
  intro hzero
  have hc := scale_pos hh hm ho
  have : oscWave hbar m omega n (y / scale hbar m omega) = 0 := by rw [hzero]; rfl
  rw [oscWave, mul_div_cancel₀ _ (ne_of_gt hc)] at this
  exact hy this

/-- Each `ψₙ` (rescaled) is an eigenfunction with energy `ℏω(n + 1/2)`. -/
theorem oscWave_isEigenstate {hbar m omega : ℝ} (hh : 0 < hbar) (hm : 0 < m) (ho : 0 < omega)
    (n : ℕ) :
    IsOscEigenstate hbar m omega (hbar * omega * ((n : ℝ) + 1 / 2)) (oscWave hbar m omega n) := by
  set c := scale hbar m omega with hc
  have hcpos : 0 < c := scale_pos hh hm ho
  have hcsq : c ^ 2 = 2 * m * omega / hbar := scale_sq hh hm ho
  refine ⟨oscWave_ne_zero hh hm ho n, fun x => c * deriv (psi n) (c * x),
    fun x => c ^ 2 * deriv (deriv (psi n)) (c * x), ?_, ?_, ?_⟩
  · intro x
    have hlin : HasDerivAt (fun t : ℝ => c * t) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have := (hasDerivAt_psi n (c * x)).comp x hlin
    rw [deriv_psi n]
    simpa [oscWave, hc, mul_comm] using this
  · intro x
    have hlin : HasDerivAt (fun t : ℝ => c * t) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have := (hasDerivAt_deriv_psi n (c * x)).comp x hlin
    rw [deriv_deriv_psi n]
    have h2 : HasDerivAt (fun x : ℝ => c * deriv (psi n) (c * x))
        (c * ((Dop (Dop (Hr n))).eval (c * x) * Real.exp (-((c * x) ^ 2 / 4)) * c)) x := by
      rw [deriv_psi n]
      exact this.const_mul c
    convert h2 using 1
    ring
  · intro x
    have heig := psi_eigen n (c * x)
    have hsecond : deriv (deriv (psi n)) (c * x)
        = ((c * x) ^ 2 / 4 - ((n : ℝ) + 1 / 2)) * psi n (c * x) := by linarith [heig]
    have hcx : (1 / 2) * m * omega ^ 2 * x ^ 2 = hbar ^ 2 / (2 * m) * c ^ 2 * ((c * x) ^ 2 / 4) := by
      rw [hcsq]
      field_simp
      ring
    have hcoef : hbar ^ 2 / (2 * m) * c ^ 2 = hbar * omega := by
      rw [hcsq]; field_simp; ring
    show -(hbar ^ 2 / (2 * m)) * (c ^ 2 * deriv (deriv (psi n)) (c * x))
      + (1 / 2) * m * omega ^ 2 * x ^ 2 * oscWave hbar m omega n x
      = hbar * omega * ((n : ℝ) + 1 / 2) * oscWave hbar m omega n x
    simp only [oscWave, ← hc]
    rw [hsecond, hcx]
    nlinarith [hcoef, psi n (c * x)]

/-- **Spectrum of the quantum harmonic oscillator.**
For `ℏ, m, ω > 0` the set of energies attained by the ladder-generated (Hermite) eigenfunctions
of `H = -(ℏ²/2m) d²/dx² + (1/2) m ω² x²` is exactly `{ℏω(n + 1/2) : n ∈ ℕ}`. -/
theorem oscillator_spectrum {hbar m omega : ℝ} (hh : 0 < hbar) (hm : 0 < m) (ho : 0 < omega) :
    {E : ℝ | ∃ n : ℕ, IsOscEigenstate hbar m omega E (oscWave hbar m omega n)}
      = {E : ℝ | ∃ n : ℕ, E = hbar * omega * ((n : ℝ) + 1 / 2)} := by
  ext E
  constructor
  · rintro ⟨n, -, f', f'', hf', hf'', heq⟩
    refine ⟨n, ?_⟩
    obtain ⟨y, hy⟩ := psi_ne_zero n
    set c := scale hbar m omega with hc
    have hcpos : 0 < c := scale_pos hh hm ho
    obtain ⟨-, g', g'', hg', hg'', heq'⟩ := oscWave_isEigenstate hh hm ho n
    have hf'g' : f' = g' := funext fun x => ((hf' x).unique (hg' x))
    have hf''g'' : f'' = g'' := by
      subst hf'g'
      exact funext fun x => ((hf'' x).unique (hg'' x))
    subst hf'g'; subst hf''g''
    have hx : oscWave hbar m omega n (y / c) ≠ 0 := by
      rw [oscWave, ← hc, mul_div_cancel₀ _ (ne_of_gt hcpos)]
      exact hy
    have h1 := heq (y / c)
    have h2 := heq' (y / c)
    have : (E - hbar * omega * ((n : ℝ) + 1 / 2)) * oscWave hbar m omega n (y / c) = 0 := by
      linarith [h1, h2]
    rcases mul_eq_zero.1 this with h | h
    · linarith [h]
    · exact absurd h hx
  · rintro ⟨n, rfl⟩
    exact ⟨n, oscWave_isEigenstate hh hm ho n⟩

end QPhys

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

