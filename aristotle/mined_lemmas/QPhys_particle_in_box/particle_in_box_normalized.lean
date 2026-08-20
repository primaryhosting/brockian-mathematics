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
