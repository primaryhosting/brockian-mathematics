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
def numVariables (C P : ℕ) : ℕ := 2 + P * C

/-- The number of independent equilibrium constraints on those variables: one normalization
condition `∑ᵢ xᵢ = 1` per phase (`P` equations), together with the equality of the chemical
potential of each of the `C` components across the `P` phases (`C * (P - 1)` equations). -/
def numConstraints (C P : ℕ) : ℕ := P + C * (P - 1)

/--
**Gibbs' phase rule**, as an affine-dimension count.

The equilibrium states of a `C`-component, `P`-phase system form the solution set of the
equilibrium constraints inside the space of intensive variables.  Modelling the constraints by
a linear map `f : V →ₗ[ℝ] W` whose source has the dimension `numVariables C P = 2 + P * C`
of the variable space and whose target has the dimension
`numConstraints C P = P + C * (P - 1)` of the constraint space, independence of the constraints
is the surjectivity of `f`, and the set of equilibrium states is the affine space `ker f`.

Its dimension — the number of degrees of freedom `F` — then satisfies `F = C - P + 2`, stated
here in the subtraction-free form `F + P = C + 2` so that it is meaningful over `ℕ`.

The proof is rank–nullity, i.e. `LinearMap.finrank_range_add_finrank_ker` in Mathlib.
-/
theorem gibbs_phase_rule
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (C P : ℕ) (hP : 1 ≤ P)
    (f : V →ₗ[ℝ] W) (hf : Function.Surjective f)
    (hV : Module.finrank ℝ V = numVariables C P)
    (hW : Module.finrank ℝ W = numConstraints C P) :
    Module.finrank ℝ (LinearMap.ker f) + P = C + 2 := by
  -- Rank–nullity for `f`.
  have key := LinearMap.finrank_range_add_finrank_ker f
  have hrange : Module.finrank ℝ (LinearMap.range f) = Module.finrank ℝ W := by
    rw [LinearMap.range_eq_top.mpr hf]
    exact finrank_top ℝ W
  rw [hrange, hV, hW] at key
  -- The remaining step is arithmetic.
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, P = p + 1 := ⟨P - 1, by omega⟩
  simp only [numVariables, numConstraints, Nat.add_sub_cancel] at key
  have hmul : (p + 1) * C = C * p + C := by ring
  rw [hmul] at key
  generalize C * p = m at key
  omega

/--
The hypotheses of `Chem.gibbs_phase_rule` are not vacuous: whenever `1 ≤ P ≤ C + 2` there is
an actual surjective constraint map with the prescribed source and target dimensions
(here the projection off a `C + 2 - P`-dimensional space of free variables).
-/
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
def degreesOfFreedom (C P : ℕ) : ℕ := C + 2 - P

/-- `Chem.gibbs_phase_rule` in the literal form `F = C - P + 2`. -/
theorem gibbs_phase_rule_dof
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (C P : ℕ) (hP : 1 ≤ P)
    (f : V →ₗ[ℝ] W) (hf : Function.Surjective f)
    (hV : Module.finrank ℝ V = numVariables C P)
    (hW : Module.finrank ℝ W = numConstraints C P) :
    Module.finrank ℝ (LinearMap.ker f) = degreesOfFreedom C P := by
  have h := gibbs_phase_rule C P hP f hf hV hW
  simp only [degreesOfFreedom]
  omega

/-- In particular the number of phases can never exceed `C + 2`: a system with more phases
than that cannot carry independent equilibrium constraints. -/
theorem phases_le (C P : ℕ) {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] (hP : 1 ≤ P)
    (f : V →ₗ[ℝ] W) (hf : Function.Surjective f)
    (hV : Module.finrank ℝ V = numVariables C P)
    (hW : Module.finrank ℝ W = numConstraints C P) :
    P ≤ C + 2 := by
  have h := gibbs_phase_rule C P hP f hf hV hW
  omega

/-- A completely explicit model, with no hypotheses beyond `1 ≤ P ≤ C + 2`, in which the phase
rule can be read off: the projection off a `C + 2 - P`-dimensional space of free variables is a
surjective constraint map of the right dimensions, and its kernel has dimension `C - P + 2`. -/
theorem gibbs_phase_rule_model (C P : ℕ) (hP : 1 ≤ P) (hPC : P ≤ C + 2) :
    Module.finrank ℝ
        (LinearMap.ker (LinearMap.fst ℝ (Fin (numConstraints C P) → ℝ)
          (Fin (C + 2 - P) → ℝ))) = degreesOfFreedom C P := by
  obtain ⟨-, -, hV, hW⟩ := gibbs_phase_rule_realizable C P hP hPC
  exact gibbs_phase_rule_dof C P hP _ LinearMap.fst_surjective hV hW

/-- A one-component system at a triple point (`C = 1`, `P = 3`) has no degrees of freedom:
the triple point is an isolated point of the phase diagram. -/
theorem one_component_triple_point
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (hf : Function.Surjective f)
    (hV : Module.finrank ℝ V = numVariables 1 3)
    (hW : Module.finrank ℝ W = numConstraints 1 3) :
    Module.finrank ℝ (LinearMap.ker f) = 0 := by
  have h := gibbs_phase_rule 1 3 (by norm_num) f hf hV hW
  omega

/-- A one-component, two-phase system (`C = 1`, `P = 2`) has one degree of freedom: its
coexistence states form a curve, e.g. the vapour-pressure curve. -/
theorem one_component_two_phase
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (hf : Function.Surjective f)
    (hV : Module.finrank ℝ V = numVariables 1 2)
    (hW : Module.finrank ℝ W = numConstraints 1 2) :
    Module.finrank ℝ (LinearMap.ker f) = 1 := by
  have h := gibbs_phase_rule 1 2 (by norm_num) f hf hV hW
  omega

/-- A one-component, single-phase system (`C = 1`, `P = 1`) has two degrees of freedom,
namely temperature and pressure. -/
theorem one_component_one_phase
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (hf : Function.Surjective f)
    (hV : Module.finrank ℝ V = numVariables 1 1)
    (hW : Module.finrank ℝ W = numConstraints 1 1) :
    Module.finrank ℝ (LinearMap.ker f) = 2 := by
  have h := gibbs_phase_rule 1 1 (by norm_num) f hf hV hW
  omega

/-- A binary two-phase system (`C = 2`, `P = 2`) has two degrees of freedom. -/
theorem binary_two_phase
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (hf : Function.Surjective f)
    (hV : Module.finrank ℝ V = numVariables 2 2)
    (hW : Module.finrank ℝ W = numConstraints 2 2) :
    Module.finrank ℝ (LinearMap.ker f) = 2 := by
  have h := gibbs_phase_rule 2 2 (by norm_num) f hf hV hW
  omega

end Chem

