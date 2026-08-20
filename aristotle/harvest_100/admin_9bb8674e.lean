/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- First derivative of `x ↦ c * sin (k * x)`. -/
lemma hasDerivAt_const_mul_sin (c k x : ℝ) :
    HasDerivAt (fun x : ℝ => c * Real.sin (k * x)) (c * k * Real.cos (k * x)) x := by
  have h : HasDerivAt (fun x : ℝ => k * x) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have := (h.sin).const_mul c
  convert this using 1
  ring

lemma deriv_const_mul_sin (c k : ℝ) :
    deriv (fun x : ℝ => c * Real.sin (k * x)) = fun x : ℝ => (c * k) * Real.cos (k * x) := by
  funext x
  simpa using (hasDerivAt_const_mul_sin c k x).deriv

/-- Second derivative of `x ↦ c * sin (k * x)`. -/
lemma deriv2_const_mul_sin (c k : ℝ) :
    deriv (deriv (fun x : ℝ => c * Real.sin (k * x)))
      = fun x : ℝ => -(c * k ^ 2) * Real.sin (k * x) := by
  rw [deriv_const_mul_sin]
  funext x
  have h : HasDerivAt (fun x : ℝ => k * x) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have := (h.cos).const_mul (c * k)
  have hd := this.deriv
  rw [hd]
  ring

/-- The eigenstates are normalized: `∫₀^L |ψ n|² = 1` for a well of positive width `L`. -/
theorem particle_in_box_normalized (L : ℝ) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..L, (Real.sqrt (2 / L) * Real.sin ((n : ℝ) * π * x / L)) ^ 2 = 1 := by
  have hL' : L ≠ 0 := ne_of_gt hL
  obtain ⟨k, hk_def⟩ : ∃ k : ℝ, k = (n : ℝ) * π / L := ⟨_, rfl⟩
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk : k ≠ 0 := by
    rw [hk_def]
    exact div_ne_zero (mul_ne_zero hn0 (ne_of_gt pi_pos)) hL'
  have harg : ∀ x : ℝ, (n : ℝ) * π * x / L = k * x := by
    intro x; rw [hk_def]; ring
  have hrw : ∀ x : ℝ, (Real.sqrt (2 / L) * Real.sin ((n : ℝ) * π * x / L)) ^ 2
      = (2 / L) * Real.sin (k * x) ^ 2 := by
    intro x
    rw [mul_pow, Real.sq_sqrt (by positivity), harg x]
  rw [intervalIntegral.integral_congr (g := fun x => (2 / L) * Real.sin (k * x) ^ 2)
      (fun x _ => hrw x)]
  rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun u => Real.sin u ^ 2) hk,
      integral_sin_sq]
  have hkL : k * L = (n : ℝ) * π := by rw [hk_def]; field_simp
  rw [smul_eq_mul, mul_zero, hkL, Real.sin_nat_mul_pi, hk_def]
  simp only [Real.sin_zero, Real.cos_zero, zero_mul, sub_zero, zero_add, sub_self]
  field_simp

/--
**Particle in a one–dimensional infinite square well of width `L`.**

For each `n ≥ 1` the normalized stationary state
`ψ n x = √(2/L) · sin (n π x / L)` vanishes at both walls `x = 0` and `x = L`,
and solves the time–independent Schrödinger equation
`-(ℏ²/(2m)) ψ'' = E ψ` with energy `E = n² π² ℏ² / (2 m L²)`.

The key Mathlib ingredients are `HasDerivAt.sin` / `HasDerivAt.cos` (for the second
derivative) and `Real.sin_nat_mul_pi` (for the boundary condition at `x = L`).
The hypothesis `1 ≤ n` is part of the physical statement (it excludes the trivial
zero state); the identities themselves also hold formally for `n = 0`.
-/
theorem particle_in_box (hbar m L : ℝ) (hm : m ≠ 0) (hL : L ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    let psi : ℝ → ℝ := fun x => Real.sqrt (2 / L) * Real.sin ((n : ℝ) * π * x / L)
    let E : ℝ := (n : ℝ) ^ 2 * π ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)
    psi 0 = 0 ∧ psi L = 0 ∧
      ∀ x : ℝ, -(hbar ^ 2 / (2 * m)) * deriv (deriv psi) x = E * psi x := by
  intro psi E
  have hpsi : psi = fun x : ℝ => Real.sqrt (2 / L) * Real.sin (((n : ℝ) * π / L) * x) := by
    funext x
    simp only [psi]
    ring_nf
  refine ⟨by simp [psi], ?_, ?_⟩
  · have : (n : ℝ) * π * L / L = (n : ℝ) * π := by
      field_simp
    simp [psi, this, Real.sin_nat_mul_pi]
  · intro x
    rw [hpsi, deriv2_const_mul_sin]
    simp only [E]
    have hs : Real.sqrt (2 / L) * Real.sin ((n : ℝ) * π / L * x)
        = Real.sqrt (2 / L) * Real.sin ((n : ℝ) * π * x / L) := by
      ring_nf
    rw [hs]
    have hL2 : L ^ 2 ≠ 0 := pow_ne_zero _ hL
    field_simp

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

