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

theorem exists_independent_constraints (C p : ℕ) (hp : p ≤ C + 1) :
    ∃ L : IntensiveSpace C p →ₗ[ℝ] ConstraintSpace C p,
      Function.Surjective L ∧
        (finrank ℝ (LinearMap.ker L) : ℤ) = (C : ℤ) - ((p : ℤ) + 1) + 2 := by
  have hle : finrank ℝ (ConstraintSpace C p) ≤ finrank ℝ (IntensiveSpace C p) := by
    rw [finrank_intensiveSpace, finrank_constraintSpace]
    have : (p + 1) * C = p * C + C := by ring
    omega
  obtain ⟨L, hL⟩ := exists_surjective_of_finrank_le hle
  exact ⟨L, hL, gibbs_phase_rule C p L hL⟩

/-- One-component, one-phase system (e.g. liquid water alone): two degrees of freedom
(temperature and pressure may be varied independently). -/
