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
lemma finrank_intensiveSpace (C p : ℕ) :
    finrank ℝ (IntensiveSpace C p) = 2 + (p + 1) * C := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype ℝ]
  simp

/-- The number of equilibrium constraints is `P + (P - 1) * C`. -/
lemma finrank_constraintSpace (C p : ℕ) :
    finrank ℝ (ConstraintSpace C p) = (p + 1) + p * C := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype ℝ,
    Module.finrank_pi_fintype ℝ]
  simp

/-- **Key intermediate lemma** (rank–nullity for the constraint map).
If the constraint map `L` is surjective, i.e. the equilibrium constraints are
independent, then the dimension of the solution set `ker L` plus the number of
constraints equals the number of variables. -/
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
theorem gibbs_phase_rule (C p : ℕ) (L : IntensiveSpace C p →ₗ[ℝ] ConstraintSpace C p)
    (hL : Function.Surjective L) :
    (finrank ℝ (LinearMap.ker L) : ℤ) = (C : ℤ) - ((p : ℤ) + 1) + 2 := by
  have h := finrank_ker_add_finrank_of_surjective L hL
  rw [finrank_intensiveSpace, finrank_constraintSpace] at h
  have h' : (finrank ℝ (LinearMap.ker L) : ℤ) + ((p : ℤ) + 1 + (p : ℤ) * C)
      = 2 + ((p : ℤ) + 1) * C := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) h
  linarith [h']

/-- Existence of a surjective linear map into a space of no larger dimension. -/
lemma exists_surjective_of_finrank_le {V W : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (h : finrank ℝ W ≤ finrank ℝ V) : ∃ L : V →ₗ[ℝ] W, Function.Surjective L := by
  classical
  set bV := Module.finBasis ℝ V
  set bW := Module.finBasis ℝ W
  refine ⟨bV.constr ℝ (fun i => if hi : (i : ℕ) < finrank ℝ W then bW ⟨i, hi⟩ else 0), ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← bW.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine ⟨bV ⟨j, lt_of_lt_of_le j.2 h⟩, ?_⟩
  rw [Basis.constr_basis]
  simp

/-- The hypothesis of `gibbs_phase_rule` is not vacuous: whenever the phase rule predicts a
nonnegative number of degrees of freedom, i.e. whenever `P = p + 1 ≤ C + 2`, there really is
a system of independent constraints, and for it the number of degrees of freedom equals
`C - P + 2`. -/
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
theorem degrees_of_freedom_one_component_one_phase :
    ∃ L : IntensiveSpace 1 0 →ₗ[ℝ] ConstraintSpace 1 0,
      Function.Surjective L ∧ (finrank ℝ (LinearMap.ker L) : ℤ) = 2 := by
  obtain ⟨L, hL, hF⟩ := exists_independent_constraints 1 0 (by norm_num)
  exact ⟨L, hL, by rw [hF]; norm_num⟩

/-- One-component, three-phase system (the triple point of water): zero degrees of
freedom, i.e. the state is isolated. -/
theorem degrees_of_freedom_triple_point :
    ∃ L : IntensiveSpace 1 2 →ₗ[ℝ] ConstraintSpace 1 2,
      Function.Surjective L ∧ (finrank ℝ (LinearMap.ker L) : ℤ) = 0 := by
  obtain ⟨L, hL, hF⟩ := exists_independent_constraints 1 2 (by norm_num)
  exact ⟨L, hL, by rw [hF]; norm_num⟩

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

