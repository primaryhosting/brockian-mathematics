import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized here

Ratner's theorems concern a one-parameter unipotent subgroup `{u_t}` of a Lie group `G` acting on
a homogeneous space `G / Γ` for a lattice `Γ`, and assert that

* the closure of every orbit is a homogeneous subset `x · H` for a closed connected subgroup `H`
  (orbit closure theorem), and
* every ergodic `u_t`-invariant probability measure is the homogeneous measure supported on such
  an orbit closure (measure classification).

This file formalizes and proves these two statements for the abelian instance
`G = ℝ²`, `Γ = ℤ²`, `u_t = (t, α t)`, i.e. the linear flow of slope `α` on the two-torus.
Here every element of `G` is unipotent, `G / Γ` is the compact homogeneous space `ℝ²/ℤ²`,
and the two conclusions read:

* `Math2.closure_orbit_eq_coset` (proved in the generality of an arbitrary topological abelian
  group): every orbit closure of a one-parameter subgroup is a coset of one fixed closed
  connected subgroup;
* `Math2.dense_orbit`: for irrational `α` the flow is minimal, so the orbit closures are the whole
  space (`H = ⊤`);
* `Math2.eq_volume_of_invariant`: for irrational `α` the flow is uniquely ergodic, i.e. Haar
  probability measure is the only invariant Borel probability measure — which is the measure
  classification statement in this setting.

The main theorem `Math2.ratner` packages the three statements together.
-/

open MeasureTheory Set Topology
open scoped BoundedContinuousFunction

namespace Math2

noncomputable section

instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The circle `ℝ / ℤ`. -/
abbrev Circle := AddCircle (1 : ℝ)

/-- The two-dimensional torus `ℝ² / ℤ²`, a homogeneous space `G / Γ` with `G = ℝ²`
(a unipotent group) and `Γ = ℤ²` a lattice. -/
abbrev Torus := Circle × Circle

/-- The one-parameter unipotent subgroup `t ↦ (t, α t)` of `ℝ²`, viewed inside the torus. -/
def uflow (α : ℝ) : ℝ →+ Torus where
  toFun t := ((t : Circle), ((α * t : ℝ) : Circle))
  map_zero' := by simp
  map_add' s t := by
    have h : α * (s + t) = α * s + α * t := by ring
    simp [h]

@[simp] lemma uflow_apply (α t : ℝ) : uflow α t = ((t : Circle), ((α * t : ℝ) : Circle)) := rfl

lemma continuous_uflow (α : ℝ) : Continuous (uflow α) := by
  apply Continuous.prodMk
  · exact continuous_quotient_mk'.comp continuous_id
  · exact continuous_quotient_mk'.comp (by fun_prop)

/-- The orbit of `x` under the unipotent flow. -/
def orbit (α : ℝ) (x : Torus) : Set Torus := Set.range fun t : ℝ => x + uflow α t

/-! ## Orbit closures are cosets of closed connected subgroups -/

section General

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

/-- The closure of the image of a one-parameter subgroup, as a subgroup. -/
def flowSubgroup (U : ℝ →+ X) : AddSubgroup X := (U.range).topologicalClosure

lemma flowSubgroup_coe (U : ℝ →+ X) :
    (flowSubgroup U : Set X) = closure (Set.range U) := by
  simp [flowSubgroup, AddSubgroup.topologicalClosure_coe, AddMonoidHom.coe_range]

lemma isClosed_flowSubgroup (U : ℝ →+ X) : IsClosed (flowSubgroup U : Set X) := by
  rw [flowSubgroup_coe]; exact isClosed_closure

lemma isConnected_flowSubgroup (U : ℝ →+ X) (hU : Continuous U) :
    IsConnected (flowSubgroup U : Set X) := by
  rw [flowSubgroup_coe]
  exact (isConnected_range hU).closure

/-- **Orbit closures are homogeneous**: in any topological abelian group, the closure of the
orbit `{x + U t}` of a one-parameter subgroup `U : ℝ →+ X` is the coset `x + H` of the closed
connected subgroup `H = closure (range U)`, which does not depend on `x`. -/
theorem closure_orbit_eq_coset (U : ℝ →+ X) (x : X) :
    closure (Set.range fun t : ℝ => x + U t) = (fun y => x + y) '' (flowSubgroup U : Set X) := by
  have h1 : (Set.range fun t : ℝ => x + U t) = (Homeomorph.addLeft x) '' (Set.range U) := by
    rw [← Set.range_comp]
    rfl
  rw [flowSubgroup_coe, h1, ← (Homeomorph.addLeft x).image_closure]
  rfl

end General

/-- The closed connected subgroup of the torus which is the closure of the unipotent
one-parameter subgroup. -/
def flowClosure (α : ℝ) : AddSubgroup Torus := flowSubgroup (uflow α)

lemma isClosed_flowClosure (α : ℝ) : IsClosed (flowClosure α : Set Torus) :=
  isClosed_flowSubgroup _

lemma isConnected_flowClosure (α : ℝ) : IsConnected (flowClosure α : Set Torus) :=
  isConnected_flowSubgroup _ (continuous_uflow α)

/-- **Orbit closure is homogeneous**: the closure of every orbit of the unipotent flow is a
coset of one fixed closed connected subgroup of the torus. -/
theorem closure_orbit_eq (α : ℝ) (x : Torus) :
    closure (orbit α x) = (fun y => x + y) '' (flowClosure α : Set Torus) :=
  closure_orbit_eq_coset (uflow α) x

/-! ## Minimality for irrational slope -/

lemma dense_zmultiples (α : ℝ) (hα : Irrational α) :
    DenseRange (fun n : ℤ => (n • α : Circle)) := by
  rw [AddCircle.denseRange_zsmul_coe_iff]
  simpa using hα

/-- **Minimality**: for irrational `α` every orbit of the unipotent flow is dense. -/
theorem dense_orbit (α : ℝ) (hα : Irrational α) (x : Torus) : Dense (orbit α x) := by
  rintro ⟨a, b⟩
  obtain ⟨t₀, ht₀⟩ : ∃ t : ℝ, (t : Circle) = a - x.1 := QuotientAddGroup.mk_surjective _
  set g : Circle → Torus := fun y => (a, x.2 + ((α * t₀ : ℝ) : Circle) + y) with hg
  have hgc : Continuous g := by fun_prop
  have hsub : g '' (Set.range fun n : ℤ => (n • (α : Circle))) ⊆ orbit α x := by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    refine ⟨t₀ + n, ?_⟩
    have hn : (((n : ℤ) : ℝ) : Circle) = 0 := by
      have hz : ((n : ℝ)) = n • (1 : ℝ) := by simp
      rw [hz, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
    have h1 : ((t₀ + (n : ℝ) : ℝ) : Circle) = a - x.1 := by
      rw [AddCircle.coe_add, ht₀, hn, add_zero]
    have h2 : ((α * (t₀ + (n : ℝ)) : ℝ) : Circle)
        = ((α * t₀ : ℝ) : Circle) + n • (α : Circle) := by
      have : α * (t₀ + (n : ℝ)) = α * t₀ + n • α := by
        rw [zsmul_eq_mul]; ring
      rw [this, AddCircle.coe_add, AddCircle.coe_zsmul]
    simp only [hg, uflow_apply, h1, h2, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    exact ⟨by abel, by abel⟩
  have hdense : Dense (Set.range fun n : ℤ => (n • (α : Circle))) := dense_zmultiples α hα
  have hmem : (a, b) ∈ g '' closure (Set.range fun n : ℤ => (n • (α : Circle))) := by
    refine ⟨b - x.2 - ((α * t₀ : ℝ) : Circle), hdense.closure_eq ▸ Set.mem_univ _, ?_⟩
    have hb : x.2 + ((α * t₀ : ℝ) : Circle) + (b - x.2 - ((α * t₀ : ℝ) : Circle)) = b := by abel
    simp [hg, hb]
  have := (image_closure_subset_closure_image hgc) hmem
  exact closure_mono hsub this

lemma dense_range_uflow (α : ℝ) (hα : Irrational α) : Dense (Set.range (uflow α)) := by
  have h := dense_orbit α hα 0
  simpa [orbit] using h

/-- For irrational `α` the closed connected subgroup occurring in the orbit closure theorem is
the whole torus. -/
lemma flowClosure_eq_top (α : ℝ) (hα : Irrational α) : flowClosure α = ⊤ := by
  rw [← AddSubgroup.coe_eq_univ, flowClosure, flowSubgroup_coe,
    (dense_range_uflow α hα).closure_eq]

/-! ## Unique ergodicity -/

instance : IsProbabilityMeasure (volume : Measure Circle) := by
  constructor
  simp [AddCircle.measure_univ]

instance : IsProbabilityMeasure (volume : Measure Torus) := by
  infer_instance

instance : (volume : Measure Torus).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- **Measure classification (unique ergodicity)**: for irrational `α`, the Haar probability
measure is the unique flow-invariant Borel probability measure on the torus. -/
theorem eq_volume_of_invariant (α : ℝ) (hα : Irrational α) (μ : Measure Torus)
    [IsProbabilityMeasure μ]
    (hinv : ∀ t : ℝ, Measure.map (fun x : Torus => x + uflow α t) μ = μ) :
    μ = (volume : Measure Torus) := by
  have hdense : Dense (Set.range (uflow α)) := dense_range_uflow α hα
  have key : ∀ f : Torus →ᵇ ℝ, ∫ x, f x ∂μ = ∫ x, f x ∂(volume : Measure Torus) := by
    intro f
    have hFc : Continuous (fun y : Torus => ∫ x, f (x + y) ∂μ) := by
      have h := continuous_parametric_integral_of_continuous
        (μ := μ) (f := fun (y : Torus) (x : Torus) => f (x + y))
        (by fun_prop) (isCompact_univ (X := Torus))
      simpa using h
    have heq : Set.EqOn (fun y : Torus => ∫ x, f (x + y) ∂μ)
        (fun _ : Torus => ∫ x, f x ∂μ) (Set.range (uflow α)) := by
      rintro _ ⟨t, rfl⟩
      have h := hinv t
      have h2 : ∫ x, f x ∂(Measure.map (fun x : Torus => x + uflow α t) μ) = ∫ x, f x ∂μ := by
        rw [h]
      rwa [integral_map (by fun_prop) f.continuous.aestronglyMeasurable] at h2
    have hFconst : ∀ y : Torus, (∫ x, f (x + y) ∂μ) = ∫ x, f x ∂μ := fun y =>
      congrFun (Continuous.ext_on hdense hFc continuous_const heq) y
    have hint : Integrable (Function.uncurry fun (y : Torus) (x : Torus) => f (x + y))
        ((volume : Measure Torus).prod μ) := by
      have : Function.uncurry (fun (y : Torus) (x : Torus) => f (x + y))
          = fun p : Torus × Torus => f (p.2 + p.1) := rfl
      rw [this]
      exact (f.compContinuous ⟨fun p : Torus × Torus => p.2 + p.1, by fun_prop⟩).integrable _
    have hswap : ∫ y, (∫ x, f (x + y) ∂μ) ∂(volume : Measure Torus)
        = ∫ x, (∫ y, f (x + y) ∂(volume : Measure Torus)) ∂μ := integral_integral_swap hint
    have hinner : ∀ x : Torus,
        (∫ y, f (x + y) ∂(volume : Measure Torus)) = ∫ y, f y ∂(volume : Measure Torus) :=
      fun x => integral_add_left_eq_self (fun y => f y) x
    calc ∫ x, f x ∂μ = ∫ y, (∫ x, f (x + y) ∂μ) ∂(volume : Measure Torus) := by
          simp [hFconst]
      _ = ∫ x, (∫ y, f (x + y) ∂(volume : Measure Torus)) ∂μ := hswap
      _ = ∫ x, f x ∂(volume : Measure Torus) := by simp [hinner]
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure key

/-! ## Ratner's theorems in this setting -/

/-- **Ratner's orbit-closure and measure-classification theorems** for the unipotent flow
`t ↦ x + (t, α t)` on the homogeneous space `ℝ²/ℤ²`:

* every orbit closure is a coset of a closed connected subgroup of the torus;
* if the slope `α` is irrational the flow is minimal (every orbit is dense);
* and in that case it is uniquely ergodic: Haar measure is the only invariant
  Borel probability measure. -/
theorem ratner :
    (∀ α : ℝ, ∃ H : AddSubgroup Torus, IsClosed (H : Set Torus) ∧ IsConnected (H : Set Torus) ∧
        ∀ x : Torus, closure (orbit α x) = (fun y => x + y) '' (H : Set Torus)) ∧
    (∀ α : ℝ, Irrational α → ∀ x : Torus, Dense (orbit α x)) ∧
    (∀ α : ℝ, Irrational α → ∀ μ : Measure Torus, IsProbabilityMeasure μ →
        (∀ t : ℝ, Measure.map (fun x : Torus => x + uflow α t) μ = μ) →
        μ = (volume : Measure Torus)) :=
  ⟨fun α => ⟨flowClosure α, isClosed_flowClosure α, isConnected_flowClosure α,
      closure_orbit_eq α⟩,
   fun α hα x => dense_orbit α hα x,
   fun α hα μ hp hinv => @eq_volume_of_invariant α hα μ hp hinv⟩

end

end Math2

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

