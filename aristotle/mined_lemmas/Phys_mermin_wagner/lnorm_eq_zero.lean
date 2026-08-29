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


theorem lnorm_eq_zero {d : ℕ} {x : Fin d → ℤ} (h : lnorm x = 0) : x = 0 := by
  funext i
  have := le_lnorm x i
  rw [h] at this
  have : (x i).natAbs = 0 := by omega
  simpa using this

/-- The key convergent shell sum: in dimension `d ≤ 2` the sum of `1 / max(‖x‖,1)^2`
over a box of size `R` grows only logarithmically. -/
