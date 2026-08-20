/-
# Box Level 7
Category: Quantum Physics
Target: QPhys.box_level_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Box Level 7
Category: Quantum Physics
Target: QPhys.box_level_7
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

/-- Energy levels of a quantum particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck constant `hbar`:
`Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For a particle in a one-dimensional infinite well, the ratio of the seventh energy
level to the ground-state energy is `7² = 49`. -/
theorem box_level_7 (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L 7 / boxEnergy hbar m L 1 = 7 ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergy
  field_simp
  ring

/-- Division-free form of the same fact, valid for all parameters (no nonvanishing
hypotheses needed): the seventh level is `7²` times the ground-state energy. -/
theorem box_level_7_eq (hbar m L : ℝ) :
    boxEnergy hbar m L 7 = 7 ^ 2 * boxEnergy hbar m L 1 := by
  unfold boxEnergy
  norm_num
  ring

/-- More generally, the ratio of the `n`-th to the `m`-th energy level of the
one-dimensional infinite well is `(n / m)²`. -/
theorem boxEnergy_ratio (hbar mass L : ℝ) (hhbar : hbar ≠ 0) (hmass : mass ≠ 0) (hL : L ≠ 0)
    (n k : ℕ) (hk : k ≠ 0) :
    boxEnergy hbar mass L n / boxEnergy hbar mass L k = ((n : ℝ) / (k : ℝ)) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  unfold boxEnergy
  field_simp

/-! ### Physical grounding: the levels `boxEnergy` really are the eigenvalues of the
time-independent Schrödinger equation on the well, for the standing waves vanishing
at both walls. -/

/-- The (unnormalised) stationary states of the one-dimensional infinite well of width
`L`: `ψₙ(x) = sin (n π x / L)`. -/
noncomputable def boxWave (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((n : ℝ) * Real.pi / L * x)

/-- The stationary states vanish at the left wall of the well. -/
theorem boxWave_zero (L : ℝ) (n : ℕ) : boxWave L n 0 = 0 := by
  simp [boxWave]

/-- The stationary states vanish at the right wall of the well. -/
theorem boxWave_at_width (L : ℝ) (hL : L ≠ 0) (n : ℕ) : boxWave L n L = 0 := by
  have : (n : ℝ) * Real.pi / L * L = (n : ℝ) * Real.pi := by field_simp
  rw [boxWave, this, Real.sin_nat_mul_pi]

/-- First derivative of the stationary state. -/
theorem deriv_boxWave (L : ℝ) (n : ℕ) :
    deriv (boxWave L n) = fun x => ((n : ℝ) * Real.pi / L) * Real.cos ((n : ℝ) * Real.pi / L * x) := by
  set c : ℝ := (n : ℝ) * Real.pi / L with hc
  funext x
  have h : HasDerivAt (fun x : ℝ => Real.sin (c * x)) (Real.cos (c * x) * (c * 1)) x :=
    HasDerivAt.sin ((hasDerivAt_id x).const_mul c)
  show deriv (fun x : ℝ => Real.sin (c * x)) x = _
  rw [show c * Real.cos (c * x) = Real.cos (c * x) * (c * 1) by ring, ← h.deriv]

/-- Second derivative of the stationary state: `ψₙ'' = -(nπ/L)² ψₙ`. -/
theorem deriv2_boxWave (L : ℝ) (n : ℕ) :
    deriv (deriv (boxWave L n)) = fun x => -(((n : ℝ) * Real.pi / L) ^ 2 * boxWave L n x) := by
  rw [deriv_boxWave]
  set c : ℝ := (n : ℝ) * Real.pi / L with hc
  funext x
  have h : HasDerivAt (fun x : ℝ => c * Real.cos (c * x)) (c * (-Real.sin (c * x) * (c * 1))) x :=
    (HasDerivAt.cos ((hasDerivAt_id x).const_mul c)).const_mul c
  show deriv (fun x : ℝ => c * Real.cos (c * x)) x = _
  rw [boxWave, show -(c ^ 2 * Real.sin (c * x)) = c * (-Real.sin (c * x) * (c * 1)) by ring,
    ← h.deriv]

/-- The stationary state `ψₙ` solves the time-independent Schrödinger equation inside the
well (where the potential vanishes), with eigenvalue `boxEnergy hbar m L n`:
`-(ħ²/2m) ψₙ'' = Eₙ ψₙ`. -/
theorem boxWave_schrodinger (hbar m L : ℝ) (hL : L ≠ 0) (n : ℕ) (x : ℝ) :
    -(hbar ^ 2 / (2 * m)) * deriv (deriv (boxWave L n)) x
      = boxEnergy hbar m L n * boxWave L n x := by
  rw [deriv2_boxWave, boxEnergy]
  rcases eq_or_ne m 0 with hm | hm
  · simp [hm]
  · field_simp

end QPhys

