import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Pointwise

namespace Chem

/-- The intensive state variables of a system with `C` chemical components distributed over
`P` phases: temperature, pressure, and the `C` mole fractions of each of the `P` phases,
i.e. `2 + P * C` real variables. -/
abbrev StateVars (C P : ℕ) : Type := Fin (2 + P * C) → ℝ

/-- The equilibrium constraints on the intensive variables: one normalization condition
`∑ mole fractions = 1` per phase (`P` equations) together with the equality of the chemical
potential of each component across consecutive phases (`C * (P - 1)` equations). -/
abbrev Constraints (C P : ℕ) : Type := Fin (P + C * (P - 1)) → ℝ

/-- Number of variables minus number of constraints, computed in `ℤ`. -/

theorem variables_sub_constraints (C P : ℕ) (hP : 1 ≤ P) :
    ((2 + P * C : ℕ) : ℤ) - ((P + C * (P - 1) : ℕ) : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  obtain ⟨Q, rfl⟩ := Nat.exists_eq_add_of_le hP
  push_cast [Nat.add_sub_cancel_left]
  ring

/-- The number of constraints never exceeds the number of variables when the constraint map
is surjective; equivalently `P ≤ C + 2`. -/
