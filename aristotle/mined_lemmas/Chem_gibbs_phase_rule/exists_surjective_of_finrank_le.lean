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

Category: Chemistry.  Target: `Chem.gibbs_phase_rule`.

## Modelling

For a heterogeneous system with `C` chemical components distributed over `P` phases, the
*intensive* state of the system is a triple `(T, p, x)` consisting of

* the temperature `T` and the pressure `p` (2 variables), and
* the mole fractions `x j i` of component `i` in phase `j` (`P * C` variables),

so the state space `Chem.StateSpace C P = ℝ × ℝ × (Fin P → Fin C → ℝ)` has
`variableCount C P = 2 + P * C` dimensions.

The equilibrium conditions are

* the normalisation `∑ i, x j i = 1` of the mole fractions in each of the `P` phases, and
* the equality of the chemical potential of each of the `C` components between consecutive
  phases, which gives `C * (P - 1)` equations,

so the constraint space `Chem.ConstraintSpace C P = (Fin P → ℝ) × (Fin (P - 1) → Fin C → ℝ)`
has `constraintCount C P = P + C * (P - 1)` dimensions.

Linearising the equilibrium conditions, they are described by a linear map
`L : StateSpace C P →ₗ[ℝ] ConstraintSpace C P`, and the (physical) assumption that the
conditions are *independent* is exactly the surjectivity of `L`.  The set of states realising
a prescribed value `c` of the constraints is then an affine subspace, namely a coset of
`ker L`, and its dimension is the number of degrees of freedom.  The theorem
`Chem.gibbs_phase_rule` computes that dimension to be `F = C - P + 2`.

`Chem.gibbs_phase_rule_coords` is the same statement written in flat coordinates
`Fin (variableCount C P) → ℝ` and `Fin (constraintCount C P) → ℝ`, and
`Chem.exists_surjective_constraintMap` shows the hypotheses are satisfiable (whenever
`1 ≤ P ≤ C + 2`), so the theorem is not vacuous.

`Chem.gibbs_phase_rule_nonlinear` upgrades the count to genuinely nonlinear equilibrium
conditions: near a regular equilibrium state, the implicit function theorem parametrises the
equilibrium set by `C - P + 2` real parameters.  Consequences of the count are
`Chem.phase_count_le` (`P ≤ C + 2`), `Chem.gibbs_invariant_point` (`P = C + 2` forces a unique
state) and `Chem.gibbs_infinite_of_phases_lt` (`P < C + 2` gives a continuum of states), and
`Chem.onePhaseRuleMap` and `Chem.triplePointMap` are explicit constraint maps realising the
classical cases `F = 1` (coexistence curve) and `F = 0` (triple point).
-/

namespace Chem

open Module Filter Topology

/-- Number of intensive variables: temperature, pressure and the `P * C` mole fractions. -/

lemma exists_surjective_of_finrank_le [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (h : finrank ℝ W ≤ finrank ℝ V) :
    ∃ L : V →ₗ[ℝ] W, Function.Surjective L := by
  set n := finrank ℝ V
  set m := finrank ℝ W
  let eV : V ≃ₗ[ℝ] (Fin n → ℝ) := (Module.finBasis ℝ V).equivFun
  let eW : W ≃ₗ[ℝ] (Fin m → ℝ) := (Module.finBasis ℝ W).equivFun
  let f : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) := LinearMap.funLeft ℝ ℝ (Fin.castLE h)
  have hf : Function.Surjective f :=
    LinearMap.funLeft_surjective_of_injective ℝ ℝ _ (Fin.castLE_injective h)
  exact ⟨eW.symm.toLinearMap ∘ₗ f ∘ₗ eV.toLinearMap,
    eW.symm.surjective.comp (hf.comp eV.surjective)⟩

/-! ### The phase rule -/

/--
**Gibbs phase rule.**

Consider a system of `C` components in `P ≥ 1` phases.  Its intensive state is a point of
`StateSpace C P = ℝ × ℝ × (Fin P → Fin C → ℝ)` (temperature, pressure, mole fractions) and the
equilibrium conditions — one mole-fraction normalisation per phase, and equality of the
chemical potential of each component between consecutive phases — are described by a linear
map `L : StateSpace C P →ₗ[ℝ] ConstraintSpace C P`, their independence being the surjectivity
of `L`.

Then for any prescribed value `c` of the constraints:

* the set of admissible states is a nonempty affine subspace, namely a coset `v₀ + ker L`, and
* its dimension — the number of degrees of freedom — equals `F = C - P + 2`.
-/
