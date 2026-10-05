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


theorem swProfile_far {d R : ℕ} (hR : 1 ≤ R) {x y : Fin d → ℤ} (hxy : adj x y)
    (hx : R < lnorm x) : swProfile d R x - swProfile d R y = 0 := by
  have h2 : lnorm x ≤ lnorm y + 1 := adj_lnorm_le (adj_symm hxy)
  unfold swProfile
  rw [prof_eq_zero hR (by omega), prof_eq_zero hR (by omega), sub_self]

end Phys

import Mathlib

/-!
# Lattice combinatorics and the two-dimensional capacity estimate

In dimension `d ≤ 2` the discrete "capacity" of a point vanishes: there are spin-wave
profiles which equal `π` at the origin, vanish outside a finite box, and have arbitrarily
small Dirichlet energy.  This is the geometric input to the Mermin–Wagner theorem.
-/

open Finset

namespace Phys

/-- The `ℓ^∞` norm on the lattice `ℤ^d`. -/
