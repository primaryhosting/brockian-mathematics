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

/-! ### Hermite polynomial facts -/

/-- The derivative of the `(n+1)`-st probabilists' Hermite polynomial. -/
theorem derivative_hermite_succ :
    ∀ n : ℕ, derivative (hermite (n + 1)) = C ((n : ℤ) + 1) * hermite n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, one_mul, ih,
        derivative_C_mul, hermite_succ n]
      push_cast [C_add, C_1]
      ring

/-- The Hermite differential equation `u'' - x u' + n u = 0`. -/
theorem hermite_ode (n : ℕ) :
    derivative (derivative (hermite n)) - X * derivative (hermite n) + C (n : ℤ) * hermite n = 0 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [derivative_hermite_succ n, derivative_C_mul, hermite_succ n]
      push_cast
      ring

/-! ### The natural-units (dimensionless) eigenfunctions -/

/-- Evaluation of the `n`-th probabilists' Hermite polynomial as a real function. -/
noncomputable def He (n : ℕ) (x : ℝ) : ℝ := aeval x (hermite n)

/-- The dimensionless Hermite–Gauss function `He n x * exp (-x²/4)`. -/
noncomputable def hermiteGauss (n : ℕ) (x : ℝ) : ℝ := He n x * Real.exp (-x ^ 2 / 4)

/-- Its first derivative, written out. -/
noncomputable def hermiteGauss' (n : ℕ) (x : ℝ) : ℝ :=
  (aeval x (derivative (hermite n)) - x / 2 * He n x) * Real.exp (-x ^ 2 / 4)

theorem hasDerivAt_gauss (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 4)) (-(x / 2) * Real.exp (-x ^ 2 / 4)) x := by
  have h : HasDerivAt (fun y : ℝ => -y ^ 2 / 4) (-(x / 2)) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 4
    simpa using this.congr_deriv (by ring)
  exact h.exp.congr_deriv (by ring)

theorem hasDerivAt_hermiteGauss (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteGauss n) (hermiteGauss' n x) x := by
  have h1 : HasDerivAt (fun y : ℝ => aeval y (hermite n)) (aeval x (derivative (hermite n))) x :=
    Polynomial.hasDerivAt_aeval _ _
  have h2 := hasDerivAt_gauss x
  have := h1.mul h2
  refine this.congr_deriv ?_
  simp only [hermiteGauss', He]
  ring

theorem hasDerivAt_hermiteGauss' (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteGauss' n)
      ((x ^ 2 / 4 - ((n : ℝ) + 1 / 2)) * hermiteGauss n x) x := by
  have hode : ∀ y : ℝ, aeval y (derivative (derivative (hermite n)))
      = y * aeval y (derivative (hermite n)) - (n : ℝ) * aeval y (hermite n) := by
    intro y
    have := congrArg (fun p : Polynomial ℤ => aeval y p) (hermite_ode n)
    simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_zero] at this
    push_cast at this
    linarith
  have h1 : HasDerivAt (fun y : ℝ => aeval y (derivative (hermite n)))
      (aeval x (derivative (derivative (hermite n)))) x :=
    Polynomial.hasDerivAt_aeval _ _
  have h0 : HasDerivAt (fun y : ℝ => aeval y (hermite n)) (aeval x (derivative (hermite n))) x :=
    Polynomial.hasDerivAt_aeval _ _
  have hid : HasDerivAt (fun y : ℝ => y / 2) (1 / 2 : ℝ) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have hA : HasDerivAt (fun y : ℝ => aeval y (derivative (hermite n)) - y / 2 * aeval y (hermite n))
      (aeval x (derivative (derivative (hermite n)))
        - (1 / 2 * aeval x (hermite n) + x / 2 * aeval x (derivative (hermite n)))) x :=
    h1.sub (hid.mul h0)
  have h2 := hasDerivAt_gauss x
  have hmul := hA.mul h2
  refine hmul.congr_deriv ?_
  simp only [hermiteGauss, He, hode x]
  ring

/-! ### The physical Landau problem -/

/-- The magnetic length scale `sqrt (ħ / (2 m ω_c))` appearing in the Landau eigenfunctions. -/
noncomputable def landauLength (hbar m omegac : ℝ) : ℝ := Real.sqrt (hbar / (2 * m * omegac))

/-- The `n`-th Landau eigenfunction (transverse factor, in the Landau gauge):
`He_n (y/ℓ) exp (-(y/ℓ)²/4)`. -/
noncomputable def landauState (hbar m omegac : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  hermiteGauss n (y / landauLength hbar m omegac)

/-- The `n`-th Landau level energy `ħ ω_c (n + 1/2)`. -/
noncomputable def landauEnergy (hbar omegac : ℝ) (n : ℕ) : ℝ := hbar * omegac * (n + 1 / 2)

theorem landauLength_pos {hbar m omegac : ℝ} (hh : 0 < hbar) (hm : 0 < m) (hw : 0 < omegac) :
    0 < landauLength hbar m omegac := by
  have : 0 < hbar / (2 * m * omegac) := by positivity
  exact Real.sqrt_pos.mpr this

theorem landauLength_sq {hbar m omegac : ℝ} (hh : 0 < hbar) (hm : 0 < m) (hw : 0 < omegac) :
    (landauLength hbar m omegac) ^ 2 = hbar / (2 * m * omegac) := by
  have : (0:ℝ) ≤ hbar / (2 * m * omegac) := by positivity
  simpa [landauLength] using Real.sq_sqrt this

theorem deriv_landauState (hbar m omegac : ℝ) (n : ℕ) :
    deriv (landauState hbar m omegac n)
      = fun y => (1 / landauLength hbar m omegac) *
          hermiteGauss' n (y / landauLength hbar m omegac) := by
  funext y
  have hin : HasDerivAt (fun z : ℝ => z / landauLength hbar m omegac)
      (1 / landauLength hbar m omegac) y := by
    simpa using (hasDerivAt_id y).div_const (landauLength hbar m omegac)
  have := (hasDerivAt_hermiteGauss n (y / landauLength hbar m omegac)).comp y hin
  exact (this.congr_deriv (by ring)).deriv

theorem deriv2_landauState {hbar m omegac : ℝ} (hh : 0 < hbar) (hm : 0 < m) (hw : 0 < omegac)
    (n : ℕ) (y : ℝ) :
    deriv (deriv (landauState hbar m omegac n)) y
      = (1 / (landauLength hbar m omegac) ^ 2) *
        (((y / landauLength hbar m omegac) ^ 2 / 4 - ((n : ℝ) + 1 / 2)) *
          landauState hbar m omegac n y) := by
  have hl : landauLength hbar m omegac ≠ 0 := ne_of_gt (landauLength_pos hh hm hw)
  rw [deriv_landauState hbar m omegac n]
  have hin : HasDerivAt (fun z : ℝ => z / landauLength hbar m omegac)
      (1 / landauLength hbar m omegac) y := by
    simpa using (hasDerivAt_id y).div_const (landauLength hbar m omegac)
  have h := ((hasDerivAt_hermiteGauss' n (y / landauLength hbar m omegac)).comp y hin).const_mul
    (1 / landauLength hbar m omegac)
  refine (h.congr_deriv ?_).deriv
  simp only [landauState]
  field_simp

/-- **Landau levels.**  A charged particle in a uniform magnetic field, reduced (in the Landau
gauge) to the one-dimensional Hamiltonian `H = -ħ²/(2m) d²/dy² + ½ m ω_c² y²` with cyclotron
frequency `ω_c`, has the Hermite–Gauss functions `landauState` as eigenfunctions, with
eigenvalues the Landau levels `E_n = ħ ω_c (n + ½)`. -/
theorem landau_levels {hbar m omegac : ℝ} (hh : 0 < hbar) (hm : 0 < m) (hw : 0 < omegac)
    (n : ℕ) (y : ℝ) :
    -(hbar ^ 2 / (2 * m)) * deriv (deriv (landauState hbar m omegac n)) y
        + 1 / 2 * m * omegac ^ 2 * y ^ 2 * landauState hbar m omegac n y
      = landauEnergy hbar omegac n * landauState hbar m omegac n y := by
  have hl : landauLength hbar m omegac ≠ 0 := ne_of_gt (landauLength_pos hh hm hw)
  have hsq := landauLength_sq hh hm hw
  rw [deriv2_landauState hh hm hw n]
  have hy : (y / landauLength hbar m omegac) ^ 2
      = y ^ 2 / (hbar / (2 * m * omegac)) := by
    rw [div_pow, hsq]
  rw [hy, landauEnergy]
  have h1 : (1 : ℝ) / (landauLength hbar m omegac) ^ 2 = 2 * m * omegac / hbar := by
    rw [hsq]
    field_simp
  rw [h1]
  have hh' : hbar ≠ 0 := ne_of_gt hh
  have hm' : m ≠ 0 := ne_of_gt hm
  have hw' : omegac ≠ 0 := ne_of_gt hw
  field_simp
  ring

/-- The Landau eigenfunctions are not identically zero, so the eigenvalue equation above is
not vacuous. -/
theorem landauState_ne_zero {hbar m omegac : ℝ} (hh : 0 < hbar) (hm : 0 < m) (hw : 0 < omegac)
    (n : ℕ) : ∃ y : ℝ, landauState hbar m omegac n y ≠ 0 := by
  have hl : landauLength hbar m omegac ≠ 0 := ne_of_gt (landauLength_pos hh hm hw)
  have hex : ∃ x : ℝ, aeval x (hermite n) ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : ((hermite n).map (Int.castRingHom ℝ)) = 0 := by
      apply Polynomial.funext
      intro x
      simpa [Polynomial.eval_map, ← Polynomial.aeval_def] using h x
    exact ((hermite_monic n).map (Int.castRingHom ℝ)).ne_zero h0
  obtain ⟨x, hx⟩ := hex
  refine ⟨x * landauLength hbar m omegac, ?_⟩
  have : x * landauLength hbar m omegac / landauLength hbar m omegac = x := by
    field_simp
  simp only [landauState, this, hermiteGauss, He]
  exact mul_ne_zero hx (Real.exp_ne_zero _)

/-- The Landau levels are equally spaced, with gap `ħ ω_c`. -/
theorem landauEnergy_succ_sub (hbar omegac : ℝ) (n : ℕ) :
    landauEnergy hbar omegac (n + 1) - landauEnergy hbar omegac n = hbar * omegac := by
  simp only [landauEnergy]
  push_cast
  ring

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

