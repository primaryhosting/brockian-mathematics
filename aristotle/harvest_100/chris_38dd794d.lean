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

theorem finrank_stateSpace (C P : ℕ) :
    Module.finrank ℝ (StateSpace C P) = 2 + P * C := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype]
  simp

theorem finrank_constraintSpace (C Q : ℕ) :
    Module.finrank ℝ (ConstraintSpace C Q) = (Q + 1) + Q * C := by
  rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi_fintype]
  simp

/-- The solution set of an inhomogeneous linear system `L v = w` with `L` surjective is a
nonempty affine subspace whose direction is `ker L`. -/
theorem vectorSpan_preimage_eq_ker {V W : Type} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W) (hL : Function.Surjective L) (w : W) :
    vectorSpan ℝ (L ⁻¹' {w}) = LinearMap.ker L := by
  obtain ⟨v0, hv0⟩ := hL w
  apply le_antisymm
  · rw [vectorSpan_def, Submodule.span_le]
    rintro x hx
    rw [Set.mem_vsub] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb
    simp [LinearMap.mem_ker, vsub_eq_sub, map_sub, ha, hb]
  · intro k hk
    have h1 : v0 + k ∈ L ⁻¹' {w} := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, map_add,
        LinearMap.mem_ker.mp hk, hv0, add_zero]
    have h2 : v0 ∈ L ⁻¹' {w} := by simp [hv0]
    exact Submodule.subset_span ⟨v0 + k, h1, v0, h2, by simp⟩

/-- **Rank–nullity form of the phase rule.**  For a surjective constraint map `L` of a system
with `C` components and `P = Q + 1` phases, the space of solutions of the homogeneous system
has dimension `C - Q + 1 = C - P + 2` (stated additively, so that no truncated natural
subtraction occurs). -/
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
theorem gibbs_phase_rule {C Q : ℕ} (L : StateSpace C (Q + 1) →ₗ[ℝ] ConstraintSpace C Q)
    (hL : Function.Surjective L) (w : ConstraintSpace C Q) :
    (L ⁻¹' {w}).Nonempty ∧
      Module.finrank ℝ (vectorSpan ℝ (L ⁻¹' {w})) + (Q + 1) = C + 2 := by
  obtain ⟨v0, hv0⟩ := hL w
  refine ⟨⟨v0, by simp [hv0]⟩, ?_⟩
  have hdir : Module.finrank ℝ (vectorSpan ℝ (L ⁻¹' {w}))
      = Module.finrank ℝ (LinearMap.ker L) := by rw [vectorSpan_preimage_eq_ker L hL w]
  have hker := finrank_ker_constraints L hL
  omega

/-- The phase rule in its familiar subtracted form `F = C - P + 2`, for `P = Q + 1` phases.
The hypothesis `Q + 1 ≤ C`, i.e. `P ≤ C`, only serves to make the truncated natural
subtraction `C - P` mean what it should. -/
theorem gibbs_phase_rule_sub {C Q : ℕ} (L : StateSpace C (Q + 1) →ₗ[ℝ] ConstraintSpace C Q)
    (hL : Function.Surjective L) (w : ConstraintSpace C Q) (hPC : Q + 1 ≤ C) :
    Module.finrank ℝ (vectorSpan ℝ (L ⁻¹' {w})) = C - (Q + 1) + 2 := by
  have h := (gibbs_phase_rule L hL w).2
  omega

/-! ### Non-vacuity: independent constraint systems do exist -/

/-- If `finrank W ≤ finrank V` then there is a surjective linear map `V →ₗ[ℝ] W`. -/
theorem exists_surjective_of_finrank_le {V W : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (h : Module.finrank ℝ W ≤ Module.finrank ℝ V) :
    ∃ L : V →ₗ[ℝ] W, Function.Surjective L := by
  classical
  let bV := Module.finBasis ℝ V
  let bW := Module.finBasis ℝ W
  refine ⟨bV.constr ℝ
    (fun i : Fin (Module.finrank ℝ V) =>
      if h' : (i : ℕ) < Module.finrank ℝ W then bW ⟨i, h'⟩ else 0), ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← bW.span_eq, Submodule.span_le]
  rintro x ⟨j, rfl⟩
  refine ⟨bV ⟨(j : ℕ), lt_of_lt_of_le j.2 h⟩, ?_⟩
  rw [Module.Basis.constr_basis]
  simp

/-- The hypotheses of `Chem.gibbs_phase_rule` are satisfiable: whenever the number of phases
`P = Q + 1` does not exceed `C + 2`, there really is an independent (surjective) constraint
map, so the phase rule is not vacuous. -/
theorem exists_surjective_constraints {C Q : ℕ} (h : Q ≤ C + 1) :
    ∃ L : StateSpace C (Q + 1) →ₗ[ℝ] ConstraintSpace C Q, Function.Surjective L := by
  apply exists_surjective_of_finrank_le
  rw [finrank_stateSpace, finrank_constraintSpace]
  have hmul : (Q + 1) * C = Q * C + C := by ring
  omega

end Chem

