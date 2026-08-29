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
def variableCount (C P : ℕ) : ℕ := 2 + P * C

/-- Number of equilibrium equations: one normalisation per phase, together with the
equalities of the chemical potentials of the `C` components between consecutive phases. -/
def constraintCount (C P : ℕ) : ℕ := P + C * (P - 1)

/-- The number of degrees of freedom predicted by the Gibbs phase rule. -/
def degreesOfFreedom (C P : ℤ) : ℤ := C - P + 2

/-- The space of intensive states: temperature, pressure, and the mole fraction `x j i` of
component `i` in phase `j`. -/
abbrev StateSpace (C P : ℕ) : Type := ℝ × ℝ × (Fin P → Fin C → ℝ)

/-- The space of values of the equilibrium conditions: one normalisation per phase, and one
chemical-potential equality per component and per pair of consecutive phases. -/
abbrev ConstraintSpace (C P : ℕ) : Type := (Fin P → ℝ) × (Fin (P - 1) → Fin C → ℝ)

/-- Arithmetic core of the phase rule: `(2 + P * C) - (P + C * (P - 1)) = C - P + 2`. -/
lemma variableCount_sub_constraintCount {C P : ℕ} (hP : 1 ≤ P) :
    (variableCount C P : ℤ) - constraintCount C P = degreesOfFreedom C P := by
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  simp only [variableCount, constraintCount, degreesOfFreedom, Nat.add_sub_cancel]
  push_cast
  ring

@[simp] lemma finrank_stateSpace (C P : ℕ) :
    finrank ℝ (StateSpace C P) = variableCount C P := by
  rw [finrank_prod, finrank_prod, Module.finrank_pi_fintype ℝ]
  simp only [finrank_self, Module.finrank_pi, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, variableCount]
  omega

@[simp] lemma finrank_constraintSpace (C P : ℕ) :
    finrank ℝ (ConstraintSpace C P) = constraintCount C P := by
  rw [finrank_prod, Module.finrank_pi, Module.finrank_pi_fintype ℝ]
  simp [constraintCount, mul_comm]

/-! ### Generic linear algebra -/

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The solution set of an inhomogeneous linear system with surjective matrix is a coset of
the kernel; in particular it is a nonempty affine subspace. -/
lemma solutionSet_eq_coset (L : V →ₗ[ℝ] W) (hL : Function.Surjective L) (c : W) :
    ∃ v₀, L v₀ = c ∧ {v | L v = c} = (fun w => v₀ + w) '' (LinearMap.ker L : Set V) := by
  obtain ⟨v₀, hv₀⟩ := hL c
  refine ⟨v₀, hv₀, ?_⟩
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker]
  constructor
  · intro hv
    exact ⟨v - v₀, by simp [map_sub, hv, hv₀], by abel⟩
  · rintro ⟨w, hw, rfl⟩
    simp [map_add, hw, hv₀]

/-- Rank–nullity for a surjective map, stated over `ℤ` so that no truncated subtraction
occurs. -/
lemma finrank_ker_of_surjective [FiniteDimensional ℝ V] (L : V →ₗ[ℝ] W)
    (hL : Function.Surjective L) :
    (finrank ℝ (LinearMap.ker L) : ℤ) = (finrank ℝ V : ℤ) - finrank ℝ W := by
  have hsum : finrank ℝ (LinearMap.range L) + finrank ℝ (LinearMap.ker L) = finrank ℝ V :=
    LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.mpr hL, finrank_top] at hsum
  have := congrArg (fun n : ℕ => (n : ℤ)) hsum
  push_cast at this
  linarith

/-- If `dim W ≤ dim V` then there is a surjective linear map `V → W`. -/
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
theorem gibbs_phase_rule {C P : ℕ} (hP : 1 ≤ P)
    (L : StateSpace C P →ₗ[ℝ] ConstraintSpace C P) (hL : Function.Surjective L)
    (c : ConstraintSpace C P) :
    (∃ v₀, L v₀ = c ∧
        {v | L v = c} = (fun w => v₀ + w) '' (LinearMap.ker L : Set (StateSpace C P)))
      ∧ (finrank ℝ (LinearMap.ker L) : ℤ) = degreesOfFreedom C P := by
  refine ⟨solutionSet_eq_coset L hL c, ?_⟩
  rw [finrank_ker_of_surjective L hL, finrank_stateSpace, finrank_constraintSpace,
    variableCount_sub_constraintCount hP]

/-- The Gibbs phase rule in flat coordinates: the state is a list of `variableCount C P`
real numbers and the equilibrium conditions are `constraintCount C P` independent linear
equations; the solution set is a coset of `ker L` of dimension `C - P + 2`. -/
theorem gibbs_phase_rule_coords {C P : ℕ} (hP : 1 ≤ P)
    (L : (Fin (variableCount C P) → ℝ) →ₗ[ℝ] (Fin (constraintCount C P) → ℝ))
    (hL : Function.Surjective L) (c : Fin (constraintCount C P) → ℝ) :
    (∃ v₀, L v₀ = c ∧
        {v | L v = c} = (fun w => v₀ + w) '' (LinearMap.ker L : Set (Fin (variableCount C P) → ℝ)))
      ∧ (finrank ℝ (LinearMap.ker L) : ℤ) = degreesOfFreedom C P := by
  refine ⟨solutionSet_eq_coset L hL c, ?_⟩
  rw [finrank_ker_of_surjective L hL, Module.finrank_pi, Module.finrank_pi]
  simpa using variableCount_sub_constraintCount (C := C) hP

/-- The hypotheses of `Chem.gibbs_phase_rule` are satisfiable exactly in the physically
meaningful range `1 ≤ P ≤ C + 2`: an independent (i.e. surjective) system of equilibrium
conditions exists there.  In particular the phase rule is not vacuous, and it also recovers
the classical bound `P ≤ C + 2` on the number of coexisting phases. -/
theorem exists_surjective_constraintMap {C P : ℕ} (hP : 1 ≤ P) (hPC : P ≤ C + 2) :
    ∃ L : StateSpace C P →ₗ[ℝ] ConstraintSpace C P, Function.Surjective L := by
  refine exists_surjective_of_finrank_le ?_
  rw [finrank_stateSpace, finrank_constraintSpace]
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  simp only [variableCount, constraintCount, Nat.add_sub_cancel]
  have h1 : (p + 1) * C = C * p + C := by ring
  omega

/-- Conversely, if the equilibrium conditions are independent then at most `C + 2` phases can
coexist. -/
theorem phase_count_le {C P : ℕ} (hP : 1 ≤ P)
    (L : StateSpace C P →ₗ[ℝ] ConstraintSpace C P) (hL : Function.Surjective L) :
    P ≤ C + 2 := by
  have h0 := finrank_ker_of_surjective L hL
  rw [finrank_stateSpace, finrank_constraintSpace] at h0
  have h : constraintCount C P ≤ variableCount C P := by
    have : (0 : ℤ) ≤ (finrank ℝ (LinearMap.ker L) : ℤ) := Int.natCast_nonneg _
    omega
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  simp only [variableCount, constraintCount, Nat.add_sub_cancel] at h
  have h1 : (p + 1) * C = C * p + C := by ring
  omega

/-- **Invariant point.**  When the maximal number of phases `P = C + 2` coexist, `F = 0` and the
equilibrium state is *unique* (for one component and three phases: the triple point). -/
theorem gibbs_invariant_point {C P : ℕ} (hP : 1 ≤ P) (hPC : P = C + 2)
    (L : StateSpace C P →ₗ[ℝ] ConstraintSpace C P) (hL : Function.Surjective L)
    (c : ConstraintSpace C P) :
    ∃! v, L v = c := by
  have hF : finrank ℝ (LinearMap.ker L) = 0 := by
    have := (gibbs_phase_rule hP L hL c).2
    simp only [degreesOfFreedom, hPC] at this
    omega
  obtain ⟨v₀, hv₀⟩ := hL c
  refine ⟨v₀, hv₀, fun v hv => ?_⟩
  have hker : LinearMap.ker L = ⊥ := Submodule.finrank_eq_zero.mp hF
  have hmem : v - v₀ ∈ LinearMap.ker L := by simp [LinearMap.mem_ker, map_sub, hv, hv₀]
  rw [hker] at hmem
  have h0 := (Submodule.mem_bot ℝ).mp hmem
  linear_combination (norm := abel) h0

/-- **Variance.**  When fewer than `C + 2` phases coexist, `F > 0` and there is a continuum of
equilibrium states (e.g. a coexistence curve for one component and two phases). -/
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
theorem gibbs_phase_rule_nonlinear {C P : ℕ} (hP : 1 ≤ P)
    (Φ : StateSpace C P → ConstraintSpace C P) (Φ' : StateSpace C P →L[ℝ] ConstraintSpace C P)
    (v₀ : StateSpace C P) (hΦ : HasStrictFDerivAt Φ Φ' v₀)
    (hsurj : LinearMap.range (Φ' : StateSpace C P →ₗ[ℝ] ConstraintSpace C P) = ⊤) :
    (finrank ℝ (LinearMap.ker (Φ' : StateSpace C P →ₗ[ℝ] ConstraintSpace C P)) : ℤ)
        = degreesOfFreedom C P ∧
      ∃ g : (LinearMap.ker (Φ' : StateSpace C P →ₗ[ℝ] ConstraintSpace C P)) → StateSpace C P,
        g 0 = v₀ ∧ (∀ᶠ y in 𝓝 0, Φ (g y) = Φ v₀) ∧
        HasStrictFDerivAt g
          (LinearMap.ker (Φ' : StateSpace C P →ₗ[ℝ] ConstraintSpace C P)).subtypeL 0 := by
  constructor
  · rw [finrank_ker_of_surjective _ (LinearMap.range_eq_top.mp hsurj), finrank_stateSpace,
      finrank_constraintSpace, variableCount_sub_constraintCount hP]
  · refine ⟨hΦ.implicitFunction Φ Φ' hsurj (Φ v₀), hΦ.implicitFunction_apply_image hsurj, ?_,
      hΦ.to_implicitFunction hsurj⟩
    have ht : Filter.Tendsto
        (fun y : (LinearMap.ker (Φ' : StateSpace C P →ₗ[ℝ] ConstraintSpace C P)) => (Φ v₀, y))
        (𝓝 0) (𝓝 (Φ v₀, 0)) := tendsto_const_nhds.prodMk_nhds tendsto_id
    exact ht.eventually (hΦ.map_implicitFunction_eq hsurj)

/-! ### A fully explicit instance: one component, two phases -/

/-- An explicit linearised constraint map for one component in two phases: the two mole-fraction
normalisations `x j 0`, together with the difference of chemical potentials
`(x 1 0 - x 0 0) + T` between the two phases in a model where the potential of a phase depends
on its composition and on the temperature. -/
def onePhaseRuleMap : StateSpace 1 2 →ₗ[ℝ] ConstraintSpace 1 2 where
  toFun v := (fun j => v.2.2 j 0, fun _ _ => v.2.2 1 0 - v.2.2 0 0 + v.1)
  map_add' u v := by ext j i <;> (simp; try ring)
  map_smul' a v := by ext j i <;> (simp; try ring)

lemma onePhaseRuleMap_surjective : Function.Surjective onePhaseRuleMap := by
  rintro ⟨r, d⟩
  refine ⟨(d 0 0 - (r 1 - r 0), 0, fun j _ => r j), ?_⟩
  ext j i
  · simp [onePhaseRuleMap]
  · show r 1 - r 0 + (d 0 0 - (r 1 - r 0)) = d j i
    have hj : j = 0 := by omega
    have hi : i = 0 := by omega
    subst hj; subst hi; ring

/-- For this explicit system (one component, two phases) the phase rule gives exactly one degree
of freedom: the coexistence curve. -/
theorem onePhaseRule_degreesOfFreedom (c : ConstraintSpace 1 2) :
    (finrank ℝ (LinearMap.ker onePhaseRuleMap) : ℤ) = 1 ∧ {v | onePhaseRuleMap v = c}.Infinite := by
  refine ⟨?_, gibbs_infinite_of_phases_lt (by norm_num) (by norm_num)
    onePhaseRuleMap onePhaseRuleMap_surjective c⟩
  have := (gibbs_phase_rule (C := 1) (P := 2) (by norm_num)
    onePhaseRuleMap onePhaseRuleMap_surjective c).2
  simpa [degreesOfFreedom] using this

/-! ### A fully explicit instance: one component, three phases (the triple point) -/

/-- An explicit linearised constraint map for one component in three phases: the three
mole-fraction normalisations, the chemical-potential difference between phases `0` and `1`
(depending on the temperature) and the difference between phases `1` and `2` (depending on the
pressure). -/
def triplePointMap : StateSpace 1 3 →ₗ[ℝ] ConstraintSpace 1 3 where
  toFun v := (fun j => v.2.2 j 0,
    fun k _ => ![v.2.2 1 0 - v.2.2 0 0 + v.1, v.2.2 2 0 - v.2.2 1 0 + v.2.1] k)
  map_add' u v := by
    ext j i
    · simp
    · fin_cases j <;> (simp; ring)
  map_smul' a v := by
    ext j i
    · simp
    · fin_cases j <;> (simp; ring)

lemma triplePointMap_surjective : Function.Surjective triplePointMap := by
  rintro ⟨r, d⟩
  refine ⟨(d 0 0 - (r 1 - r 0), d 1 0 - (r 2 - r 1), fun j _ => r j), ?_⟩
  ext j i
  · simp [triplePointMap]
  · have hi : i = 0 := by omega
    subst hi
    fin_cases j <;> (show _ = _; simp [triplePointMap])

/-- For this explicit system (one component, three phases) the phase rule gives zero degrees of
freedom, and indeed the equilibrium state is unique: the triple point. -/
theorem triplePoint_unique (c : ConstraintSpace 1 3) : ∃! v, triplePointMap v = c :=
  gibbs_invariant_point (by norm_num) (by norm_num) triplePointMap triplePointMap_surjective c

/-! ### Classical special cases -/

/-- One component, one phase: two degrees of freedom (`T` and `p` may vary freely). -/
example : degreesOfFreedom 1 1 = 2 := by decide

/-- One component, two coexisting phases: one degree of freedom (a coexistence curve). -/
example : degreesOfFreedom 1 2 = 1 := by decide

/-- One component, three coexisting phases: zero degrees of freedom (the triple point). -/
example : degreesOfFreedom 1 3 = 0 := by decide

/-- Two components, two phases: two degrees of freedom. -/
example : degreesOfFreedom 2 2 = 2 := by decide

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

