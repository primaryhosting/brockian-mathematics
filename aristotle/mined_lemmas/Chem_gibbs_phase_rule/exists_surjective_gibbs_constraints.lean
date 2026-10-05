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

set_option grind.warning false

namespace Chem

/-- The number of intensive state variables describing a heterogeneous system with
`C` chemical components distributed over `P` phases: temperature and pressure, plus,
for each phase, the `C - 1` independent mole fractions of that phase (the last one is
fixed by the requirement that the mole fractions of a phase sum to `1`). -/

theorem exists_surjective_gibbs_constraints (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P)
    (hPC : P ≤ C + 2) :
    ∃ f : (Fin (gibbsVariables C P) → ℝ) →ₗ[ℝ] (Fin (gibbsConstraints C P) → ℝ),
      Function.Surjective f := by
  have hle : gibbsConstraints C P ≤ gibbsVariables C P := by
    obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
    simp only [gibbsVariables, gibbsConstraints, Nat.add_sub_cancel]
    have h1 : (c + 1) * p = c * p + p := by ring
    have h2 : (p + 1) * c = c * p + c := by ring
    rw [h1, h2]
    omega
  refine ⟨LinearMap.funLeft ℝ ℝ (Fin.castLE hle), fun y => ?_⟩
  refine ⟨fun j => if h : (j : ℕ) < gibbsConstraints C P then y ⟨j, h⟩ else 0, ?_⟩
  funext i
  simp only [LinearMap.funLeft_apply, Fin.val_castLE, Fin.is_lt, dif_pos]

end Chem

