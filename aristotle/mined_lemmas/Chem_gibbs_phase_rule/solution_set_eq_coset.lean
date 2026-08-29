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

/-- **Counting form of the Gibbs phase rule.**

With `C ≥ 1` components distributed over `P ≥ 1` phases, the intensive state of the
system is described by `2 + P * (C - 1)` variables (temperature, pressure, and `C - 1`
independent mole fractions in each phase), while equality of the chemical potential of
each component across all phases imposes `C * (P - 1)` conditions.  The difference is
`C - P + 2`. -/

theorem solution_set_eq_coset {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ₗ[ℝ] W) (b : W) (x₀ : V) (hx₀ : f x₀ = b) :
    {x : V | f x = b} = (fun v => x₀ + v) '' (LinearMap.ker f : Set V) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker]
  constructor
  · intro hx
    refine ⟨x - x₀, ?_, by abel⟩
    simp [map_sub, hx, hx₀]
  · rintro ⟨v, hv, rfl⟩
    simp [map_add, hv, hx₀]

/-- **Gibbs phase rule** as an affine-dimension count.

Model: `V` is the space of intensive state variables of a `C`-component, `P`-phase system,
of dimension `2 + P * (C - 1)` (temperature, pressure, and `C - 1` independent mole
fractions per phase).  The equilibrium conditions are encoded by a linear map
`f : V →ₗ[ℝ] W` into the space `W` of constraint values, of dimension `C * (P - 1)`
(equality of each component's chemical potential between consecutive phases); the
constraints are assumed independent, i.e. `f` is surjective.

Then, for every attainable constraint value `b`, the set of equilibrium states is a
nonempty affine subspace — a coset of `ker f` — whose dimension, the number of degrees
of freedom, is

`F = C - P + 2`. -/
