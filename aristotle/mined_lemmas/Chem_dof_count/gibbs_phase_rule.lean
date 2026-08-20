/-
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- Number of intensive state variables of a `P`-phase, `C`-component system:
temperature and pressure, together with `C - 1` independent mole fractions in each
of the `P` phases. -/

theorem gibbs_phase_rule (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P)
    (L : (Fin (phaseVarCount C P) → ℝ) →ₗ[ℝ] (Fin (phaseConstraintCount C P) → ℝ))
    (hL : Function.Surjective L) (b : Fin (phaseConstraintCount C P) → ℝ) :
    (∃ x₀ : Fin (phaseVarCount C P) → ℝ,
        {x | L x = b} = (fun v => x₀ + v) '' (LinearMap.ker L : Set (Fin (phaseVarCount C P) → ℝ)))
      ∧ (Module.finrank ℝ (LinearMap.ker L) : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  constructor
  · obtain ⟨x₀, hx₀⟩ := hL b
    refine ⟨x₀, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker]
    constructor
    · intro hx
      exact ⟨x - x₀, by simp [map_sub, hx, hx₀], by ring⟩
    · rintro ⟨v, hv, rfl⟩
      simp [map_add, hv, hx₀]
  · have hrange : Module.finrank ℝ (LinearMap.range L) = phaseConstraintCount C P := by
      rw [LinearMap.range_eq_top.2 hL]
      simp
    have hkey := LinearMap.finrank_range_add_finrank_ker L
    rw [hrange, Module.finrank_fin_fun] at hkey
    exact dof_count C P hC hP _ hkey

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

