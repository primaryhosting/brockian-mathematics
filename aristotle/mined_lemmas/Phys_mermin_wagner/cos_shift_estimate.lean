import Mathlib

/-!
# Core of the Mermin–Wagner argument

This file contains the model-independent part of the Mermin–Wagner theorem:
a finite collection of classical `O(2)` spins with an arbitrary nonnegative,
rotation-invariant pair interaction, plus arbitrary single-site terms
(boundary conditions / external fields).

The main result `Phys.abs_magnetization_le` bounds the magnetization at a
distinguished site `o` by the *Dirichlet energy* of any "spin wave" profile
`a : V → ℝ` which equals `π` at `o` and vanishes wherever a single-site term
is present.
-/

open MeasureTheory

noncomputable instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The state space of a single classical `O(2)` (planar rotator) spin. -/
abbrev Spin := AddCircle (2 * Real.pi)

namespace Phys

section Trig


theorem cos_shift_estimate (A : Real.Angle) (s : ℝ) :
    -((A + (s : Real.Angle)).cos + (A - (s : Real.Angle)).cos - 2 * A.cos) ≤ s ^ 2 := by
  rw [angle_cos_add_real, angle_cos_sub_real]
  have h1 : -(A.cos * Real.cos s - A.sin * Real.sin s
      + (A.cos * Real.cos s + A.sin * Real.sin s) - 2 * A.cos)
      = 2 * A.cos * (1 - Real.cos s) := by ring
  rw [h1]
  have h2 : 1 - Real.cos s ≥ 0 := by nlinarith [Real.cos_le_one s]
  have h3 : A.cos ≤ 1 := (abs_le.mp (angle_abs_cos_le_one A)).2
  nlinarith [one_sub_cos_le_sq s]

end Trig

variable {V : Type*} [Fintype V]

/-- The energy of a spin configuration: a rotation-invariant pair interaction with
nonnegative couplings `J`, together with arbitrary single-site terms `G`
(these encode boundary conditions and/or external fields). -/
