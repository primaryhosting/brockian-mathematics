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

/-!
# The Gibbs phase rule as an affine dimension count

The Gibbs phase rule states that a heterogeneous system at equilibrium with `C` chemical
components distributed over `P` coexisting phases has

  `F = C - P + 2`

thermodynamic degrees of freedom.  The classical derivation is a dimension count:

* **Intensive variables.**  Temperature `T`, pressure `p`, and, for every phase `j` and every
  component `i`, the mole fraction `x i j`.  That is `2 + P * C` real variables, i.e. the
  ambient affine space is `Chem.StateSpace C P` with `dim = 2 + P * C`.

* **Equilibrium constraints.**
  - for each of the `P` phases, the mole fractions of that phase sum to `1` (`P` equations);
  - for each of the `C` components, its chemical potential agrees across all `P` phases,
    which is `C * (P - 1)` equations.

  Altogether the constraints are recorded as a map into `Chem.ConstraintSpace C Q` (with
  `P = Q + 1`), a space of dimension `(Q + 1) + Q * C = P + C * (P - 1)`.

* **Genericity.**  The count is only correct when the constraints are independent; formally,
  this is the hypothesis that the (linearised) constraint map is *surjective*.

Under these hypotheses the equilibrium locus is an affine subspace of the state space whose
dimension is
  `(2 + P * C) - (P + C * (P - 1)) = C - P + 2`,
which is the content of `Chem.gibbs_phase_rule` below.
-/

namespace Chem

/-- The space of intensive state variables of a system with `C` components and `P` phases:
temperature, pressure, and the mole fraction of each component in each phase.  Its dimension
is `2 + P * C`. -/
abbrev StateSpace (C P : ℕ) : Type := (ℝ × ℝ) × (Fin P → Fin C → ℝ)

/-- The space in which the equilibrium constraints of a system with `C` components and
`P = Q + 1` phases take their values: one real number per phase (the "mole fractions sum to
one" equations) together with one real number per component and per pair of consecutive phases
(the "equality of chemical potentials" equations).  Its dimension is
`(Q + 1) + Q * C = P + C * (P - 1)`. -/
abbrev ConstraintSpace (C Q : ℕ) : Type := (Fin (Q + 1) → ℝ) × (Fin Q → Fin C → ℝ)


theorem finrank_ker_constraints {C Q : ℕ} (L : StateSpace C (Q + 1) →ₗ[ℝ] ConstraintSpace C Q)
    (hL : Function.Surjective L) :
    Module.finrank ℝ (LinearMap.ker L) + Q = C + 1 := by
  have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hL
  have h := LinearMap.finrank_range_add_finrank_ker L
  rw [hrange] at h
  rw [finrank_top, finrank_stateSpace, finrank_constraintSpace] at h
  have hmul : (Q + 1) * C = Q * C + C := by ring
  omega

/-- **The Gibbs phase rule.**

Consider a system of `C` chemical components in `P = Q + 1` coexisting phases.  Its intensive
state is described by the `2 + P * C` variables of `Chem.StateSpace C P` (temperature,
pressure, and all mole fractions), and equilibrium is expressed by an (affine-)linear system
`L v = w` valued in `Chem.ConstraintSpace C Q`, which encodes the `P` normalisation equations
for the mole fractions together with the `C * (P - 1)` equalities of chemical potentials.
Assuming these constraints are independent (`L` surjective), the equilibrium locus is a
nonempty affine subspace of the state space, and the number `F` of its degrees of freedom —
the dimension of its direction — satisfies

  `F + P = C + 2`,  i.e.  `F = C - P + 2`. -/
