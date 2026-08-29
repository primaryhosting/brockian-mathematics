/-!
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-!
This file must literally begin with the header comment above, which Lean parses as a
module docstring; module docstrings have to precede every `import` command, so this
module is written using only Lean's core library (no `Mathlib` import) and works over
the rationals `Rat`.  The companion file `RequestProject/BoxLevel5Real.lean` states and
proves the same result over the real numbers `ℝ`, with `Real.pi` for `π`.
-/

/-- Energy of the `n`-th level of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck constant `hbar`
and circle constant `pi`:  `E n = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_eq_sq_mul (pi hbar m L : Rat) (n : Nat) :
    boxEnergy pi hbar m L n = (n : Rat) ^ 2 * boxEnergy pi hbar m L 1 := by
  unfold boxEnergy
  have h1 : ((1 : Nat) : Rat) ^ 2 = 1 := by decide
  rw [h1, Rat.one_mul, Rat.mul_assoc, rat_mul_div, rat_mul_div]

/-- Dividing a multiple of a nonzero rational by that rational. -/
