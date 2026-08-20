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

lemma finrank_ker_add_finrank_of_surjective
    {V W : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W) (hL : Function.Surjective L) :
    finrank ℝ (LinearMap.ker L) + finrank ℝ W = finrank ℝ V := by
  have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hL
  have h := LinearMap.finrank_range_add_finrank_ker L
  rw [hrange] at h
  rw [add_comm]
  simpa using h

/-- **Gibbs phase rule.**

Consider a heterogeneous chemical system with `C` components and `P = p + 1` phases at
equilibrium. Its intensive state is described by the temperature, the pressure and the
`P * C` mole fractions, i.e. by a point of `IntensiveSpace C p`, of dimension `2 + P * C`.
Equilibrium imposes the linear-in-count family of constraints valued in
`ConstraintSpace C p`, of dimension `P + (P - 1) * C`: one closure relation per phase and,
for each component, equality of its chemical potential across consecutive phases.

If these constraints are independent (the constraint map `L` is surjective), then the set
of equilibrium states is the affine (here linear) subspace `ker L`, whose dimension — the
number of degrees of freedom `F` — is

  `F = C - P + 2`. -/
