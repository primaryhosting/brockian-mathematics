import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
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

namespace QPhys

/-- The `n`-th stationary state of a particle in an infinite square well of width `L`,
`ψ_n(x) = √(2/L) · sin(nπx/L)`. -/

theorem boxState_normalized (L : ℝ) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0 : ℝ)..L, (boxState L n x) ^ 2 = 1 := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set c : ℝ := (n : ℝ) * Real.pi / L with hcdef
  have hc : c ≠ 0 := by
    have : (0 : ℝ) < c := by
      apply div_pos (mul_pos hn' Real.pi_pos) hL
    exact ne_of_gt this
  have hfun : ∀ x : ℝ, (boxState L n x) ^ 2 = (2 / L) * Real.sin (c * x) ^ 2 := by
    intro x
    have h2 : Real.sqrt (2 / L) ^ 2 = 2 / L := by
      rw [Real.sq_sqrt]
      positivity
    have : (n : ℝ) * Real.pi * x / L = c * x := by
      rw [hcdef]; ring
    rw [boxState, this, mul_pow, h2]
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => y / 2 - Real.sin (2 * c * y) / (4 * c))
        (Real.sin (c * x) ^ 2) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => 2 * c * y) (2 * c) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * c)
    have hsin := (Real.hasDerivAt_sin (2 * c * x)).comp x hlin
    have h1 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
      simpa using (hasDerivAt_id x).div_const 2
    have := h1.sub (hsin.div_const (4 * c))
    convert this using 1
    have hcos : Real.cos (2 * c * x) = 1 - 2 * Real.sin (c * x) ^ 2 := by
      rw [show (2 : ℝ) * c * x = 2 * (c * x) by ring, Real.cos_two_mul']
      linarith [Real.sin_sq_add_cos_sq (c * x)]
    rw [hcos]
    field_simp
    linarith [Real.sin_sq_add_cos_sq (c * x)]
  have hint : ∫ x in (0 : ℝ)..L, Real.sin (c * x) ^ 2
      = (L / 2 - Real.sin (2 * c * L) / (4 * c)) - (0 / 2 - Real.sin (2 * c * 0) / (4 * c)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    apply Continuous.intervalIntegrable
    fun_prop
  have hsinL : Real.sin (2 * c * L) = 0 := by
    have : 2 * c * L = (2 * n : ℕ) * Real.pi := by
      rw [hcdef]; push_cast; field_simp
    rw [this, Real.sin_nat_mul_pi]
  have hsin0 : Real.sin (2 * c * 0) = 0 := by simp
  simp only [hfun]
  rw [intervalIntegral.integral_const_mul, hint, hsinL, hsin0]
  field_simp
  ring

/--
**Particle in a box.**  For a well of width `L > 0` and a particle of mass `m > 0`, the
normalized wave function `ψ_n(x) = √(2/L) sin(nπx/L)` with `n ≥ 1` vanishes at both walls,
is normalized on `[0, L]`, and solves the time-independent Schrödinger equation
`-ℏ²/(2m) ψ'' = E_n ψ` with energy `E_n = n²π²ℏ²/(2mL²)`.

The hypothesis `1 ≤ n` is part of the physical statement (it labels the admissible energy
levels); the identities themselves hold for every `n : ℕ`.
-/
