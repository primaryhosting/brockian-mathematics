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

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`E_n = n² π² ℏ² / (2 m L²)`. -/

lemma boxWave_normalized {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in (0 : ℝ)..L, (boxWave L n x) ^ 2 = 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hk : ((n : ℝ) * Real.pi / L) ≠ 0 := by positivity
  have hsq : (Real.sqrt (2 / L)) ^ 2 = 2 / L := Real.sq_sqrt (by positivity)
  have hpt : ∀ x : ℝ, (boxWave L n x) ^ 2
      = (2 / L) * Real.sin ((n : ℝ) * Real.pi / L * x) ^ 2 := by
    intro x; rw [boxWave, mul_pow, hsq]
  rw [intervalIntegral.integral_congr
      (g := fun x => (2 / L) * Real.sin ((n : ℝ) * Real.pi / L * x) ^ 2) (fun x _ => hpt x),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun y => Real.sin y ^ 2) hk, integral_sin_sq]
  have h1 : (n : ℝ) * Real.pi / L * L = (n : ℝ) * Real.pi := by field_simp
  rw [mul_zero, h1, Real.sin_nat_mul_pi]
  simp only [Real.sin_zero, Real.cos_zero, smul_eq_mul]
  field_simp
  ring

/-- **Existence of the levels.** For every `n ≥ 1` the function `ψ_n` is a bound state of the
infinite square well with energy `E_n = n²π²ℏ²/(2mL²)`. -/
