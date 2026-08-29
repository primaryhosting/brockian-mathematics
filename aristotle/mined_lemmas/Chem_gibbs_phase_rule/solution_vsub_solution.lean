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

theorem solution_vsub_solution (C P : ℕ) (L : StateVars C P →ₗ[ℝ] Constraints C P)
    (hL : Function.Surjective L) (b : Constraints C P) :
    {x : StateVars C P | L x = b} -ᵥ {x : StateVars C P | L x = b}
      = (LinearMap.ker L : Set (StateVars C P)) := by
  obtain ⟨x₀, hx₀⟩ := hL b
  ext v
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    simp only [Set.mem_setOf_eq] at hx hy
    simp [LinearMap.mem_ker, vsub_eq_sub, map_sub, hx, hy]
  · intro hv
    refine ⟨x₀ + v, ?_, x₀, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, map_add, hx₀]
      simpa [LinearMap.mem_ker] using congrArg (fun w => b + w) (LinearMap.mem_ker.mp hv)
    · simpa using hx₀
    · simp [vsub_eq_sub]

/-- **Gibbs phase rule, affine form.**  The affine set of equilibrium states
`{x | L x = b}` has affine dimension `F = C - P + 2`. -/
