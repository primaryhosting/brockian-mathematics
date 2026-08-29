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

theorem exists_surjective_constraints (C P : ℕ) (hP : 1 ≤ P) (hPC : P ≤ C + 2) :
    ∃ L : StateVars C P →ₗ[ℝ] Constraints C P, Function.Surjective L := by
  have hle : P + C * (P - 1) ≤ 2 + P * C := by
    obtain ⟨Q, rfl⟩ := Nat.exists_eq_add_of_le hP
    simp only [Nat.add_sub_cancel_left]
    have : (1 + Q) * C = C * Q + C := by ring
    omega
  refine ⟨LinearMap.funLeft ℝ ℝ (Fin.castLE hle), ?_⟩
  exact LinearMap.funLeft_surjective_of_injective ℝ ℝ _ (Fin.castLE_injective hle)

/-- The set of equilibrium states, i.e. the solutions of the constraint equations `L x = b`,
is an affine subset whose difference set is exactly the kernel of `L`. -/
