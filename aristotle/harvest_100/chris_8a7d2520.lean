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

/-
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Set MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- The state space of a first-order linear system of `n` equations. -/
abbrev State (n : ℕ) : Type := Fin n → ℂ

variable {n : ℕ}

/-- *Weak regularity* of the coefficient family of the first-order linear system
`u' t = A t (u t)`: the coefficient operators depend continuously on time.  This is the
hypothesis retained in the Weyl-theoretic statement below. -/
def WeakRegularity (A : ℝ → (State n →L[ℂ] State n)) : Prop := Continuous A

/-- The space of (everywhere differentiable, global) solutions of the linear system
`u' t = A t (u t)`. -/
def solutions (A : ℝ → (State n →L[ℂ] State n)) : Submodule ℂ (ℝ → State n) where
  carrier := {u | ∀ t, HasDerivAt u (A t (u t)) t}
  add_mem' {u v} hu hv := by
    intro t
    simpa [map_add] using (hu t).add (hv t)
  zero_mem' := by
    intro t
    simpa using (hasDerivAt_const t (0 : State n))
  smul_mem' c u hu := by
    intro t
    simpa [map_smul] using (hu t).const_smul c

/-- The subspace of square-integrable functions `ℝ → State n` (with respect to Lebesgue
measure); membership in this space is what turns a solution of the differential equation
into a deficiency vector. -/
def sqIntegrable (n : ℕ) : Submodule ℂ (ℝ → State n) where
  carrier := {u | MemLp u 2 volume}
  add_mem' hu hv := hu.add hv
  zero_mem' := MeasureTheory.MemLp.zero
  smul_mem' c _ hu := hu.const_smul c

/-- The **deficiency space** of the differential system: the square-integrable solutions of
`u' t = A t (u t)`.  In Weyl's theory (with `A` built from the differential expression
`τ - z`) this is exactly the deficiency subspace of the associated minimal operator. -/
def deficiencySpace (A : ℝ → (State n →L[ℂ] State n)) : Submodule ℂ (ℝ → State n) :=
  solutions A ⊓ sqIntegrable n

/-- Evaluation of a deficiency vector at time `0`, i.e. its initial data, as a linear map
into the finite dimensional space `ℂⁿ`. -/
def deficiencyEval (A : ℝ → (State n →L[ℂ] State n)) :
    deficiencySpace A →ₗ[ℂ] State n where
  toFun u := (u : ℝ → State n) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Uniqueness for the linear system: a solution vanishing at one time vanishes
identically. -/
theorem solution_eq_zero_of_apply_eq_zero {A : ℝ → (State n →L[ℂ] State n)}
    (hA : WeakRegularity A) {u : ℝ → State n} (hu : ∀ t, HasDerivAt u (A t (u t)) t)
    {t₀ : ℝ} (h0 : u t₀ = 0) : u = 0 := by
  funext t
  obtain ⟨a, b, ht, ht₀⟩ : ∃ a b, t ∈ Ioo a b ∧ t₀ ∈ Ioo a b :=
    ⟨min t t₀ - 1, max t t₀ + 1, ⟨by
        have := min_le_left t t₀; linarith, by have := le_max_left t t₀; linarith⟩,
      ⟨by have := min_le_right t t₀; linarith, by have := le_max_right t t₀; linarith⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hA.continuousOn
  set K : NNReal := ⟨max C 0, le_max_right _ _⟩ with hK
  have hvK : ∀ s ∈ Ioo a b, LipschitzOnWith K (fun x : State n => A s x) univ := by
    intro s hs
    have hle : ‖A s‖₊ ≤ K := by
      have h1 : ‖A s‖ ≤ C := hC s (Ioo_subset_Icc_self hs)
      simpa [hK, ← NNReal.coe_le_coe] using le_trans h1 (le_max_left C 0)
    exact ((A s).lipschitz.weaken hle).lipschitzOnWith
  have hzero : ∀ s : ℝ, HasDerivAt (fun _ : ℝ => (0 : State n)) (A s ((0 : ℝ → State n) s)) s := by
    intro s
    simpa using (hasDerivAt_const s (0 : State n))
  have heq : EqOn u (fun _ : ℝ => (0 : State n)) (Ioo a b) := by
    refine ODE_solution_unique_of_mem_Ioo (v := fun s x => A s x) (s := fun _ => univ)
      hvK ht₀ (fun s _ => ⟨hu s, mem_univ _⟩) (fun s _ => ⟨hzero s, mem_univ _⟩) ?_
    simpa using h0
  simpa using heq ht

/-- The deficiency space is faithfully represented by the initial data of the ODE: the
evaluation map is injective. -/
theorem deficiencyEval_injective {A : ℝ → (State n →L[ℂ] State n)} (hA : WeakRegularity A) :
    Function.Injective (deficiencyEval A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  have hu : ∀ t, HasDerivAt (m : ℝ → State n) (A t ((m : ℝ → State n) t)) t := m.2.1
  have h0 : (m : ℝ → State n) 0 = 0 := hm
  exact Subtype.ext (solution_eq_zero_of_apply_eq_zero hA hu h0)

/-- **Deficiency represents the ODE.**  For a weakly regular first-order linear system of
order `n`, the deficiency space (square-integrable solutions) embeds into the space of
initial data `ℂⁿ` via evaluation; in particular its dimension is at most `n`, which is the
classical Weyl bound on deficiency indices. -/
theorem deficiencyRepresentsODE_of_weakRegularity {A : ℝ → (State n →L[ℂ] State n)}
    (hA : WeakRegularity A) :
    Function.Injective (deficiencyEval A) ∧
      Module.finrank ℂ (deficiencySpace A) ≤ n := by
  refine ⟨deficiencyEval_injective hA, ?_⟩
  have h := LinearMap.finrank_le_finrank_of_injective (f := deficiencyEval A)
    (deficiencyEval_injective hA)
  simpa using h

/-! ### Non-vacuity: a weakly regular system with a nonzero deficiency space -/

/-- The scalar coefficient `A t = -2t` of the equation `u' = -2t u`, whose solutions are the
multiples of the Gaussian. -/
noncomputable def gaussCoeff : ℝ → (State 1 →L[ℂ] State 1) :=
  fun t => ((-2 * t : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (State 1)

/-- The Gaussian `t ↦ exp (-t²)`, viewed as a one-component state. -/
noncomputable def gaussSol : ℝ → State 1 := fun t _ => ((Real.exp (-t ^ 2) : ℝ) : ℂ)

theorem weakRegularity_gaussCoeff : WeakRegularity gaussCoeff := by
  unfold WeakRegularity gaussCoeff
  fun_prop

theorem gaussSol_mem_deficiencySpace : gaussSol ∈ deficiencySpace gaussCoeff := by
  constructor
  · intro t
    have hr : HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2)) (Real.exp (-t ^ 2) * (-(2 * t))) t := by
      have h1 : HasDerivAt (fun s : ℝ => -s ^ 2) (-(2 * t)) t := by
        simpa using (hasDerivAt_pow 2 t).neg
      simpa using h1.exp
    have hc : HasDerivAt (fun s : ℝ => ((Real.exp (-s ^ 2) : ℝ) : ℂ))
        (((Real.exp (-t ^ 2) * (-(2 * t)) : ℝ) : ℂ)) t := hr.ofReal_comp
    rw [hasDerivAt_pi]
    intro i
    simpa [gaussSol, gaussCoeff, Complex.ofReal_mul, mul_comm] using hc
  · have hnorm : ∀ t : ℝ, ‖gaussSol t‖ = Real.exp (-t ^ 2) := by
      intro t
      unfold gaussSol
      simp [Pi.norm_def, Complex.norm_exp, -Complex.ofReal_pow]
    have hcont : Continuous gaussSol := by
      unfold gaussSol; exact continuous_pi fun _ => by fun_prop
    show MemLp gaussSol 2 volume
    rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
    have hI : Integrable (fun t : ℝ => Real.exp (-2 * t ^ 2)) volume :=
      integrable_exp_neg_mul_sq (by norm_num)
    refine hI.congr ?_
    filter_upwards with t
    rw [hnorm t, show (-2 * t ^ 2 : ℝ) = (-t ^ 2) + (-t ^ 2) by ring, Real.exp_add]
    ring

/-- The bound proved above is not vacuous: there are weakly regular systems whose deficiency
space is nonzero. -/
theorem deficiencySpace_gaussCoeff_ne_bot : deficiencySpace gaussCoeff ≠ ⊥ := by
  intro h
  have h0 : gaussSol = 0 := by
    have := (Submodule.mem_bot ℂ (x := gaussSol)).1 (h ▸ gaussSol_mem_deficiencySpace)
    exact this
  have : ((Real.exp (-(0 : ℝ) ^ 2) : ℝ) : ℂ) = 0 := congrFun (congrFun h0 0) 0
  simp at this

end Brockian.Weyl.DeficiencyODE

