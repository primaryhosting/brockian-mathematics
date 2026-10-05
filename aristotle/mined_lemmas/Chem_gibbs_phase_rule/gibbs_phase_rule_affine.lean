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

theorem gibbs_phase_rule_affine (C P : ℕ) (hP : 1 ≤ P) (L : StateVars C P →ₗ[ℝ] Constraints C P)
    (hL : Function.Surjective L) (b : Constraints C P) :
    (Module.finrank ℝ (vectorSpan ℝ {x : StateVars C P | L x = b}) : ℤ)
      = (C : ℤ) - (P : ℤ) + 2 := by
  have hspan : vectorSpan ℝ {x : StateVars C P | L x = b} = LinearMap.ker L := by
    rw [vectorSpan_def, solution_vsub_solution C P L hL b, Submodule.span_eq]
  rw [hspan]
  exact gibbs_phase_rule C P hP L hL

end Chem

import Mathlib

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

