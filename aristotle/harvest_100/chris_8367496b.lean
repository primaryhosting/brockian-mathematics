/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is a plain comment and is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Real

/-- The (unnormalized-constant times) `n`-th stationary state of the infinite square
well of width `L`: `ψ n x = c * sin (n π x / L)`. -/
noncomputable def psi (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (2 / L) * Real.sin (n * π * x / L)

/-- The `n`-th energy level of the infinite square well of width `L`,
for a particle of mass `m` with reduced Planck constant `hbar`. -/
noncomputable def E (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * π ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The inner linear map `x ↦ n π x / L` has derivative `n π / L`. -/
lemma hasDerivAt_arg (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (n : ℝ) * π * x / L) ((n : ℝ) * π / L) x := by
  simpa [mul_div_assoc] using (((hasDerivAt_id x).const_mul ((n : ℝ) * π)).div_const L)

lemma hasDerivAt_psi (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (psi L n)
      (Real.sqrt (2 / L) * (((n : ℝ) * π / L) * Real.cos (n * π * x / L))) x := by
  have h2 := ((hasDerivAt_arg L n x).sin).const_mul (Real.sqrt (2 / L))
  convert h2 using 1
  ring

lemma deriv_psi (L : ℝ) (n : ℕ) :
    deriv (psi L n) = fun x => Real.sqrt (2 / L) * ((n * π / L) * Real.cos (n * π * x / L)) := by
  funext x; exact (hasDerivAt_psi L n x).deriv

lemma hasDerivAt_deriv_psi (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (deriv (psi L n)) (-(((n : ℝ) * π / L) ^ 2) * psi L n x) x := by
  rw [deriv_psi]
  have h2 := (((hasDerivAt_arg L n x).cos).const_mul ((n : ℝ) * π / L)).const_mul
    (Real.sqrt (2 / L))
  convert h2 using 1
  simp [psi]; ring

lemma deriv2_psi (L : ℝ) (n : ℕ) :
    deriv (deriv (psi L n)) = fun x => -(((n : ℝ) * π / L) ^ 2) * psi L n x := by
  funext x; exact (hasDerivAt_deriv_psi L n x).deriv

/-- Antiderivative computation: `∫ sin (k x)² dx = x/2 - sin (2 k x)/(4 k)`. -/
lemma integral_sin_sq_lin (k : ℝ) (hk : k ≠ 0) (a b : ℝ) :
    ∫ x in a..b, Real.sin (k * x) ^ 2
      = (b / 2 - Real.sin (2 * k * b) / (4 * k)) - (a / 2 - Real.sin (2 * k * a) / (4 * k)) := by
  have H : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => x / 2 - Real.sin (2 * k * x) / (4 * k)) (Real.sin (k * x) ^ 2) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => 2 * k * x) (2 * k) x := by
      simpa using ((hasDerivAt_id x).const_mul (2 * k))
    have h3 := (((hasDerivAt_id x).div_const 2).sub ((h1.sin).div_const (4 * k)))
    have hc : Real.cos (2 * k * x) = 1 - 2 * Real.sin (k * x) ^ 2 := by
      rw [show (2 : ℝ) * k * x = 2 * (k * x) by ring, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (k * x)]
    convert h3 using 1
    rw [hc]; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => H x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]

/-- The states `ψ_n` are normalized on the well `[0, L]`. -/
lemma psi_normalized (L : ℝ) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..L, (psi L n x) ^ 2 = 1 := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk : (n : ℝ) * π / L ≠ 0 := div_ne_zero (mul_ne_zero hn0 Real.pi_ne_zero) hL'
  have hrw : (fun x => (psi L n x) ^ 2)
      = fun x => (2 / L) * Real.sin (((n : ℝ) * π / L) * x) ^ 2 := by
    funext x
    rw [psi, show (n : ℝ) * π * x / L = ((n : ℝ) * π / L) * x from by ring, mul_pow,
      Real.sq_sqrt (by positivity)]
  rw [show (∫ x in (0:ℝ)..L, (psi L n x) ^ 2)
      = ∫ x in (0:ℝ)..L, (2 / L) * Real.sin (((n : ℝ) * π / L) * x) ^ 2 by rw [hrw]]
  rw [intervalIntegral.integral_const_mul, integral_sin_sq_lin _ hk]
  have h0 : Real.sin (2 * ((n : ℝ) * π / L) * L) = 0 := by
    have h : 2 * ((n : ℝ) * π / L) * L = ((2 * n : ℕ) : ℝ) * π := by push_cast; field_simp
    rw [h, Real.sin_nat_mul_pi]
  rw [h0]
  simp [hL']

/-- **Particle in a box.**  For the infinite square well of width `L > 0`, the
functions `ψ_n (x) = √(2/L) · sin (n π x / L)` (`n ≥ 1`) vanish at both walls
`x = 0` and `x = L`, are normalized on `[0, L]`, and solve the time-independent
Schrödinger equation `-(ℏ²/2m) ψ'' = E ψ` with energy
`E_n = n² π² ℏ² / (2 m L²)`. -/
theorem particle_in_box (hbar m L : ℝ) (hm : m ≠ 0) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    psi L n 0 = 0 ∧ psi L n L = 0 ∧ (∫ x in (0:ℝ)..L, (psi L n x) ^ 2) = 1 ∧
      ∀ x : ℝ, -(hbar ^ 2 / (2 * m)) * deriv (deriv (psi L n)) x
        = E hbar m L n * psi L n x := by
  refine ⟨by simp [psi], ?_, psi_normalized L hL n hn, ?_⟩
  · have : (n : ℝ) * π * L / L = n * π := by field_simp
    rw [psi, this, Real.sin_nat_mul_pi]
    ring
  · intro x
    rw [deriv2_psi, E]
    have hL' : L ≠ 0 := ne_of_gt hL
    field_simp

/-- Every energy level `E_n` with `n ≥ 1` is positive (for `m, L > 0` and `ℏ ≠ 0`);
in particular the ground state energy `E_1 = π²ℏ²/(2mL²)` is nonzero. -/
theorem energy_levels_pos (hbar m L : ℝ) (hbar0 : hbar ≠ 0) (hm : 0 < m) (hL : 0 < L)
    (n : ℕ) (hn : 1 ≤ n) : 0 < E hbar m L n := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have : (0:ℝ) < hbar ^ 2 := by positivity
  unfold E
  positivity

/-- The energy levels increase strictly with `n`. -/
theorem energy_levels_strictMono (hbar m L : ℝ) (hbar0 : hbar ≠ 0) (hm : 0 < m) (hL : 0 < L) :
    StrictMono (fun n : ℕ => E hbar m L n) := by
  have hb : (0:ℝ) < hbar ^ 2 := by positivity
  intro a b hab
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have ha : (0:ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hsq : (a : ℝ) ^ 2 < (b : ℝ) ^ 2 := by nlinarith
  have hden : (0:ℝ) < 2 * m * L ^ 2 := by positivity
  have hpi : (0:ℝ) < π ^ 2 := by positivity
  have hnum : (a : ℝ) ^ 2 * π ^ 2 * hbar ^ 2 < (b : ℝ) ^ 2 * π ^ 2 * hbar ^ 2 :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hsq hpi) hb
  simp only [E]
  gcongr

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

