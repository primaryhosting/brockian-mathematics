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

lemma boxState_schrodinger (hm : 0 < m) (hL : 0 < L) (x : ℝ) :
    -(hbar ^ 2 / (2 * m)) * deriv (deriv (boxState L n)) x
      = boxEnergy hbar m L n * boxState L n x := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hm0 : m ≠ 0 := ne_of_gt hm
  set a : ℝ := (n : ℝ) * π / L with ha
  have hstate : boxState L n = fun x => Real.sqrt (2 / L) * Real.sin (a * x) := rfl
  have hd1 : ∀ x, HasDerivAt (boxState L n) (Real.sqrt (2 / L) * (Real.cos (a * x) * a)) x := by
    intro x
    rw [hstate]
    exact ((hasDerivAt_lin a x).sin).const_mul _
  have hderiv1 : deriv (boxState L n) = fun x => Real.sqrt (2 / L) * (Real.cos (a * x) * a) := by
    funext x; exact (hd1 x).deriv
  have hd2 : ∀ x, HasDerivAt (deriv (boxState L n))
      (Real.sqrt (2 / L) * (-(Real.sin (a * x)) * a * a)) x := by
    intro x
    rw [hderiv1]
    have hc : HasDerivAt (fun y => Real.cos (a * y) * a) (-(Real.sin (a * x)) * a * a) x := by
      have h := ((hasDerivAt_lin a x).cos).mul_const a
      convert h using 1
    exact hc.const_mul _
  have hderiv2 : deriv (deriv (boxState L n))
      = fun x => Real.sqrt (2 / L) * (-(Real.sin (a * x)) * a * a) := by
    funext x; exact (hd2 x).deriv
  rw [hderiv2, hstate]
  simp only [boxEnergy]
  have haa : a ^ 2 = (n : ℝ) ^ 2 * π ^ 2 / L ^ 2 := by rw [ha]; ring
  have key : -(hbar ^ 2 / (2 * m)) * (Real.sqrt (2 / L) * (-(Real.sin (a * x)) * a * a))
      = (hbar ^ 2 / (2 * m)) * a ^ 2 * (Real.sqrt (2 / L) * Real.sin (a * x)) := by ring
  rw [key, haa]
  field_simp

/-- The stationary states are normalized on `[0, L]`. -/
