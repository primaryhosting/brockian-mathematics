/-
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

/-- The number of intensive state variables describing a heterogeneous system with `C`
components distributed over `P` phases: the temperature, the pressure, and, for every one of
the `P` phases, the `C` mole fractions of the components in that phase. -/

theorem gibbs_phase_rule_realizable (C P : ℕ) (hP : 1 ≤ P) (hPC : P ≤ C + 2) :
    ∃ f : ((Fin (numConstraints C P) → ℝ) × (Fin (C + 2 - P) → ℝ)) →ₗ[ℝ]
          (Fin (numConstraints C P) → ℝ),
      Function.Surjective f ∧
      Module.finrank ℝ ((Fin (numConstraints C P) → ℝ) × (Fin (C + 2 - P) → ℝ))
        = numVariables C P ∧
      Module.finrank ℝ (Fin (numConstraints C P) → ℝ) = numConstraints C P := by
  refine ⟨LinearMap.fst ℝ _ _, LinearMap.fst_surjective, ?_, Module.finrank_fin_fun ℝ⟩
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, P = p + 1 := ⟨P - 1, by omega⟩
  simp only [numVariables, numConstraints, Nat.add_sub_cancel]
  have hmul : (p + 1) * C = C * p + C := by ring
  rw [hmul]
  generalize C * p = m
  omega

/-- The number of degrees of freedom predicted by the phase rule, `F = C - P + 2`. -/
