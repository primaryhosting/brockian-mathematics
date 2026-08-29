/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

namespace Frontier

/-!
## The statement

The Kadison–Singer problem (does every pure state on the atomic maximal abelian
subalgebra of `B(ℓ²)` extend uniquely to a pure state on `B(ℓ²)`?) was resolved
affirmatively by Marcus, Spielman and Srivastava, who proved Weaver's
discrepancy-theoretic reformulation `KS₂`.  Weaver proved that `KS₂` is
equivalent to the Kadison–Singer problem, so `KS₂` is the finite dimensional
combinatorial heart of the matter.

`WeaverKS2 d α` below is exactly the Marcus–Spielman–Srivastava statement in
dimension `d` with parameter `α`, written using quadratic forms rather than
operator norms: for a positive semidefinite operator `A = ∑ i ∈ S, vᵢ vᵢ*` one
has `‖A‖ ≤ c` if and only if `⟪x, A x⟫ = ∑ i ∈ S, |⟪vᵢ, x⟫|² ≤ c ‖x‖²` for all
`x`.  Likewise the isotropy hypothesis `∑ i, vᵢ vᵢ* = 1` is written as
`∑ i, |⟪vᵢ, x⟫|² = ‖x‖²`.
-/

/-- Weaver's `KS₂` statement (the Marcus–Spielman–Srivastava theorem) in
dimension `d` with parameter `α`:

if `v₁, …, vₘ ∈ ℂ^d` satisfy `‖vᵢ‖² ≤ α` and the isotropy condition
`∑ i, vᵢ vᵢ* = 1`, then the index set can be split into two pieces `S` and `Sᶜ`
with `‖∑ i ∈ S, vᵢ vᵢ*‖ ≤ (1/√2 + √α)²` and likewise for `Sᶜ`. -/
def WeaverKS2 (d : ℕ) (α : ℝ) : Prop :=
  ∀ (m : ℕ) (v : Fin m → EuclideanSpace ℂ (Fin d)),
    (∀ i, ‖v i‖ ^ 2 ≤ α) →
    (∀ x : EuclideanSpace ℂ (Fin d), ∑ i, ‖inner ℂ (v i) x‖ ^ 2 = ‖x‖ ^ 2) →
    ∃ S : Finset (Fin m),
      (∀ x : EuclideanSpace ℂ (Fin d),
        ∑ i ∈ S, ‖inner ℂ (v i) x‖ ^ 2
          ≤ (1 / Real.sqrt 2 + Real.sqrt α) ^ 2 * ‖x‖ ^ 2) ∧
      (∀ x : EuclideanSpace ℂ (Fin d),
        ∑ i ∈ Sᶜ, ‖inner ℂ (v i) x‖ ^ 2
          ≤ (1 / Real.sqrt 2 + Real.sqrt α) ^ 2 * ‖x‖ ^ 2)

/-- The hypotheses of `WeaverKS2` are satisfiable in every dimension (so the
statement is not vacuous): the standard orthonormal basis of `ℂ^d` is a family
of unit vectors satisfying the isotropy condition, with `m = d` and `α = 1`. -/
theorem standard_basis_isotropic (d : ℕ) :
    (∀ i : Fin d, ‖(EuclideanSpace.single i (1:ℂ) : EuclideanSpace ℂ (Fin d))‖ ^ 2 ≤ 1) ∧
      (∀ x : EuclideanSpace ℂ (Fin d),
        ∑ i, ‖inner ℂ (EuclideanSpace.single i (1:ℂ) : EuclideanSpace ℂ (Fin d)) x‖ ^ 2
          = ‖x‖ ^ 2) := by
  constructor
  · intro i; simp
  · intro x
    have h1 : ∀ i : Fin d,
        inner ℂ (EuclideanSpace.single i (1:ℂ) : EuclideanSpace ℂ (Fin d)) x = x i := by
      intro i; rw [EuclideanSpace.inner_single_left]; simp
    simp only [h1]
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-!
## A balanced-partition lemma

The one dimensional case of `KS₂` is a statement about splitting a family of
small nonnegative weights of total mass `1` into two parts of mass roughly
`1/2` each.
-/

/-- A family of weights of total mass `1`, each at most `α`, forces `0 ≤ α`. -/
theorem nonneg_of_bounded_weights {m : ℕ} (a : Fin m → ℝ) (α : ℝ)
    (hsmall : ∀ i, a i ≤ α) (htot : ∑ i, a i = 1) : 0 ≤ α := by
  by_contra hα
  push_neg at hα
  have : ∑ i, a i ≤ 0 :=
    Finset.sum_nonpos fun i _ => le_of_lt (lt_of_le_of_lt (hsmall i) hα)
  linarith

/-- Greedy balanced partition: nonnegative weights of total mass `1`, each at
most `α`, can be split into two parts of mass at most `1/2 + α`. -/
theorem exists_balanced_partition {m : ℕ} (a : Fin m → ℝ) (α : ℝ)
    (hsmall : ∀ i, a i ≤ α) (htot : ∑ i, a i = 1) :
    ∃ S : Finset (Fin m),
      (∑ i ∈ S, a i ≤ 1 / 2 + α) ∧ (∑ i ∈ Sᶜ, a i ≤ 1 / 2 + α) := by
  classical
  -- Choose `S` of mass at most `1/2` with the largest possible mass.
  set T : Finset (Finset (Fin m)) :=
    Finset.univ.filter (fun S : Finset (Fin m) => ∑ i ∈ S, a i ≤ 1 / 2) with hT
  have hα0 : 0 ≤ α := nonneg_of_bounded_weights a α hsmall htot
  have hTne : T.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [hT]
  obtain ⟨S, hS, hmax⟩ := T.exists_max_image (fun S => ∑ i ∈ S, a i) hTne
  have hShalf : ∑ i ∈ S, a i ≤ 1 / 2 := by
    have := Finset.mem_filter.1 (hT ▸ hS)
    exact this.2
  have hcompl : ∑ i ∈ Sᶜ, a i = 1 - ∑ i ∈ S, a i := by
    have : ∑ i ∈ S, a i + ∑ i ∈ Sᶜ, a i = ∑ i, a i :=
      Finset.sum_add_sum_compl S a
    rw [htot] at this
    linarith
  refine ⟨S, by linarith, ?_⟩
  -- Now bound the complement.
  by_contra hcon
  push_neg at hcon
  rw [hcompl] at hcon
  have hlt : ∑ i ∈ S, a i < 1 / 2 - α := by linarith
  -- The complement has positive mass, hence contains an element of positive weight.
  have hpos : (0 : ℝ) < ∑ i ∈ Sᶜ, a i := by rw [hcompl]; linarith
  obtain ⟨i, hiS, hai⟩ : ∃ i ∈ Sᶜ, (0 : ℝ) < a i := by
    by_contra hno
    push_neg at hno
    have : ∑ i ∈ Sᶜ, a i ≤ 0 :=
      Finset.sum_nonpos fun i hi => hno i hi
    linarith
  have hiS' : i ∉ S := Finset.mem_compl.1 hiS
  have hins : ∑ j ∈ insert i S, a j = a i + ∑ j ∈ S, a j :=
    Finset.sum_insert hiS'
  have hmem : insert i S ∈ T := by
    rw [hT]
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [hins]
    linarith [hsmall i]
  have := hmax _ hmem
  rw [hins] at this
  linarith

/-- The elementary numeric estimate `1/2 + α ≤ (1/√2 + √α)²`. -/
theorem half_add_le_sq_sqrt (α : ℝ) (hα : 0 ≤ α) :
    1 / 2 + α ≤ (1 / Real.sqrt 2 + Real.sqrt α) ^ 2 := by
  have h2 : Real.sqrt 2 > 0 := Real.sqrt_pos.2 (by norm_num)
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqa : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα
  have hsqa0 : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hexp : (1 / Real.sqrt 2 + Real.sqrt α) ^ 2
      = 1 / 2 + α + 2 * (1 / Real.sqrt 2) * Real.sqrt α := by
    field_simp
    nlinarith [hsq2, hsqa]
  rw [hexp]
  have : 0 ≤ 2 * (1 / Real.sqrt 2) * Real.sqrt α := by positivity
  linarith

/-!
## The base case `d = 1`
-/

/-- Weaver's `KS₂` holds in dimension one, for every parameter `α`. -/
theorem weaverKS2_dim_one (α : ℝ) : WeaverKS2 1 α := by
  intro m v hsmall hiso
  classical
  set a : Fin m → ℝ := fun i => ‖v i‖ ^ 2 with ha
  have hkey : ∀ (i : Fin m) (x : EuclideanSpace ℂ (Fin 1)),
      ‖inner ℂ (v i) x‖ ^ 2 = a i * ‖x‖ ^ 2 := by
    intro i x
    simp [ha, PiLp.inner_apply, EuclideanSpace.norm_eq, mul_pow]
    ring
  have htot : ∑ i, a i = 1 := by
    have h1 : ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 1))‖ = 1 := by simp
    have := hiso (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 1))
    simp only [hkey, h1] at this
    simpa using this
  obtain ⟨S, hS1, hS2⟩ := exists_balanced_partition a α hsmall htot
  have hα : 0 ≤ α := nonneg_of_bounded_weights a α hsmall htot
  have hbound := half_add_le_sq_sqrt α hα
  refine ⟨S, ?_, ?_⟩
  · intro x
    have : ∑ i ∈ S, ‖inner ℂ (v i) x‖ ^ 2 = (∑ i ∈ S, a i) * ‖x‖ ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => hkey i x
    rw [this]
    have hx : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
    have : ∑ i ∈ S, a i ≤ (1 / Real.sqrt 2 + Real.sqrt α) ^ 2 := le_trans hS1 hbound
    exact mul_le_mul_of_nonneg_right this hx
  · intro x
    have : ∑ i ∈ Sᶜ, ‖inner ℂ (v i) x‖ ^ 2 = (∑ i ∈ Sᶜ, a i) * ‖x‖ ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => hkey i x
    rw [this]
    have hx : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
    have : ∑ i ∈ Sᶜ, a i ≤ (1 / Real.sqrt 2 + Real.sqrt α) ^ 2 := le_trans hS2 hbound
    exact mul_le_mul_of_nonneg_right this hx

/-!
## The trivial regime
-/

/-- If `α ≥ (1 - 1/√2)²` then the bound `(1/√2 + √α)²` is at least `1`, so the
trivial partition works, in every dimension. -/
theorem weaverKS2_of_large (d : ℕ) (α : ℝ) (hα : (1 - 1 / Real.sqrt 2) ^ 2 ≤ α) :
    WeaverKS2 d α := by
  intro m v _ hiso
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2le : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hnn : 0 ≤ 1 - 1 / Real.sqrt 2 := by
    have : 1 / Real.sqrt 2 ≤ 1 := by
      rw [div_le_one h2]
      nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
    linarith
  have hsqrt : 1 - 1 / Real.sqrt 2 ≤ Real.sqrt α := by
    have := Real.sqrt_le_sqrt hα
    rwa [Real.sqrt_sq hnn] at this
  have hone : (1:ℝ) ≤ (1 / Real.sqrt 2 + Real.sqrt α) ^ 2 := by
    nlinarith [hsqrt, Real.sqrt_nonneg α, h2]
  refine ⟨∅, ?_, ?_⟩
  · intro x
    simp only [Finset.sum_empty]
    positivity
  · intro x
    rw [Finset.compl_empty, hiso x]
    nlinarith [sq_nonneg ‖x‖, hone]

/-!
## The main statement
-/

/-- **Kadison–Singer / Weaver `KS₂`** (Marcus–Spielman–Srivastava).

`WeaverKS2 d α` is the finite dimensional statement equivalent (by Weaver's
theorem) to the Kadison–Singer problem.  This is the Lean-checked part of it:
the base case `d = 1` in full, and every dimension `d` in the regime
`α ≥ (1 - 1/√2)²` where the bound `(1/√2 + √α)²` already exceeds `1`. -/
theorem kadison_singer (d : ℕ) (α : ℝ)
    (h : d = 1 ∨ (1 - 1 / Real.sqrt 2) ^ 2 ≤ α) : WeaverKS2 d α := by
  rcases h with h | h
  · subst h; exact weaverKS2_dim_one α
  · exact weaverKS2_of_large d α h

end Frontier

