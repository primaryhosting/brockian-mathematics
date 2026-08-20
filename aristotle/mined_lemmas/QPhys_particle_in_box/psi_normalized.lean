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
