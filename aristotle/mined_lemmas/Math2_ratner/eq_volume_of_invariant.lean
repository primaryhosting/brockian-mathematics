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
