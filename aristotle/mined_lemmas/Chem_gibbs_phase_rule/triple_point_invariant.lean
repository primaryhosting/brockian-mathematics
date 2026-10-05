import Mathlib
/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-!
## Modelling

Consider a heterogeneous system with `C` chemical components distributed over `P` phases at
equilibrium.  The intensive state of the system is described by

* temperature and pressure: `2` variables;
* the composition of each phase: `C - 1` independent mole fractions per phase (the last one is
  fixed by the normalisation `∑ xᵢ = 1`), hence `P * (C - 1)` variables.

So the ambient space of intensive variables is (an open subset of) an affine space of dimension

`n = P * (C - 1) + 2`,

which we model by the coordinate space `Fin (P * (C - 1) + 2) → ℝ`.

The equilibrium conditions are the equalities of chemical potentials of each component across the
phases, `μᵢ⁽¹⁾ = μᵢ⁽²⁾ = ⋯ = μᵢ⁽ᴾ⁾` for `i = 1, …, C`; that is `(P - 1) * C` independent
scalar constraints, modelled by a linear map

`f : (Fin (P * (C - 1) + 2) → ℝ) →ₗ[ℝ] (Fin ((P - 1) * C) → ℝ)`

whose independence is expressed by the surjectivity of `f`.  The set of equilibrium states is the
(affine) solution set of `f`, whose dimension equals `Module.finrank ℝ (LinearMap.ker f)`.

The Gibbs phase rule is then exactly the rank–nullity computation of that dimension.  The key
Mathlib ingredient is `LinearMap.finrank_range_add_finrank_ker`
(rank–nullity: `finrank (range f) + finrank (ker f) = finrank V`).
-/

/-- **Gibbs phase rule.**  For a system of `C ≥ 1` components in `P ≥ 1` phases, model the
intensive variables (temperature, pressure and the `C - 1` independent mole fractions in each of
the `P` phases) by the space `Fin (P * (C - 1) + 2) → ℝ`, and the `(P - 1) * C` independent
equilibrium conditions (equality of chemical potentials across phases) by a surjective linear map
`f` onto `Fin ((P - 1) * C) → ℝ`.  Then the number of degrees of freedom, i.e. the dimension of
the solution set `ker f`, is

`F = C - P + 2`.

The identity is stated in `ℤ` so that no truncated subtraction occurs. -/

theorem triple_point_invariant
    (f : (Fin (3 * (1 - 1) + 2) → ℝ) →ₗ[ℝ] (Fin ((3 - 1) * 1) → ℝ))
    (hf : Function.Surjective f) :
    Module.finrank ℝ (LinearMap.ker f) = 0 := by
  have h := gibbs_phase_rule 1 3 le_rfl (by norm_num) f hf
  norm_num at h
  rw [h, finrank_bot]

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

