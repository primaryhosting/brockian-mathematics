import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`Eₙ = n²π²ℏ²/(2mL²)`. -/

lemma boxState_normalized (hL : 0 < L) (hn : 1 ≤ n) :
    ∫ x in (0 : ℝ)..L, boxState L n x ^ 2 = 1 := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  set a : ℝ := (n : ℝ) * π / L with ha
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha0 : 0 < a := by rw [ha]; positivity
  have hsq : Real.sqrt (2 / L) ^ 2 = 2 / L := Real.sq_sqrt (by positivity)
  have h1 : ∀ x : ℝ, boxState L n x ^ 2 = (2 / L) * Real.sin (a * x) ^ 2 := by
    intro x
    show (Real.sqrt (2 / L) * Real.sin (a * x)) ^ 2 = _
    rw [mul_pow, hsq]
  rw [intervalIntegral.integral_congr (g := fun x => (2 / L) * Real.sin (a * x) ^ 2)
    (fun x _ => h1 x), intervalIntegral.integral_const_mul]
  have h2 : ∫ x in (0 : ℝ)..L, Real.sin (a * x) ^ 2 = a⁻¹ • ∫ y in (a * 0)..(a * L), Real.sin y ^ 2 :=
    intervalIntegral.integral_comp_mul_left (fun y => Real.sin y ^ 2) (ne_of_gt ha0)
  rw [h2]
  have haL : a * L = (n : ℝ) * π := by rw [ha]; field_simp
  rw [haL, mul_zero, integral_sin_sq]
  simp [Real.sin_nat_mul_pi]
  field_simp
  rw [← haL]; ring

end Eigenstates

/-- **Particle in a box.**  For a particle of mass `m > 0` in an infinite square well of
width `L > 0` (with reduced Planck constant `ℏ > 0`):

1. for every `n ≥ 1`, the function `ψₙ(x) = √(2/L)·sin(nπx/L)` vanishes at both walls,
   is normalized on `[0, L]`, and solves the time-independent Schrödinger equation
   `-(ℏ²/2m)·ψₙ'' = Eₙ·ψₙ` with `Eₙ = n²π²ℏ²/(2mL²)`;
2. conversely, these are the *only* possible energies: any twice-differentiable solution
   of `-(ℏ²/2m)·ψ'' = E·ψ` with `ψ(0) = ψ(L) = 0` which is not identically zero has
   `E = Eₙ` for some `n ≥ 1`. -/
