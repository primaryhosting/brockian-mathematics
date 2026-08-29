import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

/-- Index set of the intensive variables of a heterogeneous system with `C` components
distributed over `P` phases: the two field variables (temperature and pressure), encoded by
`Bool`, together with the mole fraction `x j i` of component `i` in phase `j`.
Hence there are `2 + P * C` variables. -/
abbrev VarIndex (C P : ℕ) : Type := Bool ⊕ (Fin P × Fin C)

/-- Index set of the equilibrium constraints: one normalization condition
`∑ i, x j i = 1` per phase `j` (that is `P` conditions), together with the equalities of
chemical potentials between consecutive phases, `μ i (j) = μ i (j+1)`, one for each component
`i` and each of the `P - 1` consecutive pairs of phases.
Hence there are `P + (P - 1) * C` constraints. -/
abbrev ConIndex (C P : ℕ) : Type := Fin P ⊕ (Fin (P - 1) × Fin C)

/-- The number of intensive variables is `2 + P * C`. -/

theorem gibbs_phase_rule_explicit (C P : ℕ) (hP : 1 ≤ P)
    (mu : Fin P → Fin C → ((VarIndex C P → ℝ) →ₗ[ℝ] ℝ))
    (hmu : Function.Surjective (constraintMap C P mu)) :
    (Module.finrank ℝ (LinearMap.ker (constraintMap C P mu)) : ℤ) = (C : ℤ) - (P : ℤ) + 2 ∧
      ∃ x₀ : VarIndex C P → ℝ,
        {x : VarIndex C P → ℝ |
            (∀ j : Fin P, ∑ i, x (Sum.inr (j, i)) = 1) ∧
            (∀ (k : Fin (P - 1)) (i : Fin C),
              mu (phaseLo k) i x = mu (phaseHi k) i x)}
          = {x : VarIndex C P → ℝ | x - x₀ ∈ LinearMap.ker (constraintMap C P mu)} := by
  obtain ⟨hdim, x₀, hx₀⟩ :=
    gibbs_phase_rule C P hP (constraintMap C P mu) hmu
      (Sum.elim (fun _ => 1) (fun _ => 0))
  refine ⟨hdim, x₀, ?_⟩
  rw [← hx₀]
  ext x
  simp only [Set.mem_setOf_eq, funext_iff, Sum.forall, Prod.forall, constraintMap,
    LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr, sub_eq_zero]

/-- An unconditional form of the phase rule: for any physically meaningful data
(`1 ≤ C` components, `1 ≤ P ≤ C + 2` phases) there exist linearized chemical potentials whose
equilibrium constraints are independent, and for those the space of equilibrium states has
dimension exactly `F = C - P + 2`. -/
