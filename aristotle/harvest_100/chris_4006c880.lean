import Mathlib

/-!
# Box Level 2
Category: Quantum Physics
Target: QPhys.box_level_2
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

/-- The `n`-th stationary state of a particle of mass `m` in a one-dimensional
infinite square well ("particle in a box") of width `L`, up to normalization:
`ψ_n(x) = sin (n π x / L)`.  It vanishes at both walls `x = 0` and `x = L`. -/
noncomputable def boxState (L : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => Real.sin ((n : ℝ) * Real.pi / L * x)

/-- The `n`-th energy level of a particle of mass `m` in a one-dimensional infinite
square well of width `L`, with reduced Planck constant `hbar`:
`E_n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- `boxState L n` vanishes at the left wall. -/
theorem boxState_zero (L : ℝ) (n : ℕ) : boxState L n 0 = 0 := by
  simp [boxState]

/-- `boxState L n` vanishes at the right wall, so it satisfies the boundary
conditions of the infinite well. -/
theorem boxState_width (L : ℝ) (hL : L ≠ 0) (n : ℕ) : boxState L n L = 0 := by
  have : (n : ℝ) * Real.pi / L * L = (n : ℝ) * Real.pi := by
    field_simp
  simp [boxState, this, Real.sin_nat_mul_pi]

/-- Second derivative of a sine wave. -/
private theorem deriv_deriv_sin_mul (c x : ℝ) :
    deriv (deriv (fun y : ℝ => Real.sin (c * y))) x = -(Real.sin (c * x) * c ^ 2) := by
  have h : deriv (fun y : ℝ => Real.sin (c * y)) = fun y => Real.cos (c * y) * c := by
    funext y
    exact (by
      simpa using (Real.hasDerivAt_sin (c * y)).comp y ((hasDerivAt_id y).const_mul c) :
      HasDerivAt (fun z : ℝ => Real.sin (c * z)) (Real.cos (c * y) * c) y).deriv
  rw [h]
  have h2 : HasDerivAt (fun y : ℝ => Real.cos (c * y) * c) (-(Real.sin (c * x) * c ^ 2)) x := by
    have := ((Real.hasDerivAt_cos (c * x)).comp x ((hasDerivAt_id x).const_mul c)).mul_const c
    simpa using this.congr_deriv (by ring)
  exact h2.deriv

/-- `boxState L n` is an eigenfunction of the free Hamiltonian `-ħ²/(2m) d²/dx²`
inside the well, with eigenvalue `boxEnergy hbar m L n`.  This justifies the
formula used for the energy levels. -/
theorem boxState_isEigen (hbar m L : ℝ) (hm : m ≠ 0) (hL : L ≠ 0) (n : ℕ) (x : ℝ) :
    -hbar ^ 2 / (2 * m) * deriv (deriv (boxState L n)) x
      = boxEnergy hbar m L n * boxState L n x := by
  have hb : boxState L n = fun y : ℝ => Real.sin ((n : ℝ) * Real.pi / L * y) := rfl
  have h := deriv_deriv_sin_mul ((n : ℝ) * Real.pi / L) x
  rw [hb, h]
  simp only [boxEnergy]
  field_simp

/-- **Box Level 2.**  For a particle in a one-dimensional infinite square well,
the ratio of the second energy level to the ground state energy is `2² = 4`. -/
theorem box_level_2 (hbar m L : ℝ) (hbar0 : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L 2 / boxEnergy hbar m L 1 = 2 ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [boxEnergy]
  rw [div_div_div_cancel_right₀]
  · field_simp
    ring
  · exact mul_ne_zero (mul_ne_zero two_ne_zero hm) (pow_ne_zero 2 hL)

/-- More generally, the energy levels of the infinite square well scale as `n²`. -/
theorem boxEnergy_ratio (hbar m L : ℝ) (hbar0 : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) (n : ℕ) :
    boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [boxEnergy]
  rw [div_div_div_cancel_right₀]
  · field_simp
    norm_num
  · exact mul_ne_zero (mul_ne_zero two_ne_zero hm) (pow_ne_zero 2 hL)

end QPhys

