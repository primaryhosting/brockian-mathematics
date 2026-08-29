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

theorem gibbs_infinite_of_phases_lt {C P : ℕ} (hP : 1 ≤ P) (hPC : P < C + 2)
    (L : StateSpace C P →ₗ[ℝ] ConstraintSpace C P) (hL : Function.Surjective L)
    (c : ConstraintSpace C P) :
    {v | L v = c}.Infinite := by
  have hF : 0 < finrank ℝ (LinearMap.ker L) := by
    have := (gibbs_phase_rule hP L hL c).2
    simp only [degreesOfFreedom] at this
    omega
  obtain ⟨v₀, hv₀⟩ := hL c
  have hne : LinearMap.ker L ≠ ⊥ := by
    intro hbot; rw [hbot] at hF; simp at hF
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply Set.infinite_of_injective_forall_mem (f := fun t : ℝ => v₀ + t • w)
  · intro a b hab
    simp only [add_right_inj] at hab
    have hsub : (a - b) • w = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp hsub with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hw0
  · intro t
    simp [Set.mem_setOf_eq, map_add, map_smul, LinearMap.mem_ker.mp hw, hv₀]

/-! ### The nonlinear phase rule

The equilibrium conditions of a real system are not linear in `(T, p, x)`: the chemical potentials
are nonlinear functions of the state.  The implicit function theorem upgrades the linear count to
the genuine statement: near a *regular* equilibrium state (one where the differential of the
conditions is surjective), the set of equilibrium states is parametrised by `C - P + 2` real
parameters.
-/

/--
**Gibbs phase rule, nonlinear form.**

Let `Φ : StateSpace C P → ConstraintSpace C P` collect the equilibrium conditions of a system of
`C` components in `P ≥ 1` phases (mole-fraction normalisations and chemical-potential equalities),
as an arbitrary — in particular nonlinear — function of the intensive state.  Assume `Φ` is
strictly differentiable at a state `v₀` with surjective differential `Φ'` (`v₀` is a regular
equilibrium state).  Then:

* the space `ker Φ'` of admissible infinitesimal variations has dimension `F = C - P + 2`, and
* there is a local parametrisation `g : ker Φ' → StateSpace C P` of the equilibrium set through
  `v₀`: `g 0 = v₀`, `Φ (g y) = Φ v₀` for all `y` near `0`, and `g` is strictly differentiable at
  `0` with derivative the inclusion `ker Φ' → StateSpace C P`.

So the equilibrium states near `v₀` really do form an `F`-parameter family with `F = C - P + 2`.
-/
