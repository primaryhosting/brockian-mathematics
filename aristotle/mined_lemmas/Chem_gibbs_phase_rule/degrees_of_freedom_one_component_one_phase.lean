/-
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Module

/-- The space of intensive state variables of a heterogeneous system with `C` chemical
components distributed over `P = p + 1` phases: the temperature and the pressure
(the two entries of the `ℝ × ℝ` factor), together with, for every phase, the
composition vector listing the mole fraction of each component in that phase. -/
abbrev IntensiveSpace (C p : ℕ) : Type := (ℝ × ℝ) × (Fin (p + 1) → Fin C → ℝ)

/-- The space in which the equilibrium constraints of a system with `C` components and
`P = p + 1` phases take their values: one scalar per phase (the closure relation saying
that the mole fractions of that phase sum to `1`) together with, for each of the `p`
consecutive pairs of phases, one scalar per component (equality of the chemical potential
of that component in the two phases). -/
abbrev ConstraintSpace (C p : ℕ) : Type := (Fin (p + 1) → ℝ) × (Fin p → Fin C → ℝ)

/-- The number of intensive variables is `2 + P * C`. -/

theorem degrees_of_freedom_one_component_one_phase :
    ∃ L : IntensiveSpace 1 0 →ₗ[ℝ] ConstraintSpace 1 0,
      Function.Surjective L ∧ (finrank ℝ (LinearMap.ker L) : ℤ) = 2 := by
  obtain ⟨L, hL, hF⟩ := exists_independent_constraints 1 0 (by norm_num)
  exact ⟨L, hL, by rw [hF]; norm_num⟩

/-- One-component, three-phase system (the triple point of water): zero degrees of
freedom, i.e. the state is isolated. -/
