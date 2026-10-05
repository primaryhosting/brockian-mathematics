import Mathlib

/-!
# Core of the Mermin–Wagner argument

This file contains the model-independent part of the Mermin–Wagner theorem:
a finite collection of classical `O(2)` spins with an arbitrary nonnegative,
rotation-invariant pair interaction, plus arbitrary single-site terms
(boundary conditions / external fields).

The main result `Phys.abs_magnetization_le` bounds the magnetization at a
distinguished site `o` by the *Dirichlet energy* of any "spin wave" profile
`a : V → ℝ` which equals `π` at `o` and vanishes wherever a single-site term
is present.
-/

open MeasureTheory

noncomputable instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The state space of a single classical `O(2)` (planar rotator) spin. -/
abbrev Spin := AddCircle (2 * Real.pi)

namespace Phys

section Trig


theorem abs_magnetization_le {J : V → V → ℝ} {G : V → Spin → ℝ} {β : ℝ} {a : V → ℝ}
    (hJ : ∀ x y, 0 ≤ J x y) (hG : ∀ x, Continuous (G x))
    (hβ : 0 < β) (hGa : ∀ x, a x ≠ 0 → G x = 0)
    (o : V) (ho : a o = Real.pi) :
    |gibbsAvg β (energy J G) fun θ => Real.Angle.cos (θ o)|
      ≤ (Real.exp (β * dirichlet J a / 2) - 1) / 2 := by
  set sa : V → Spin := fun x => ((a x : ℝ) : Spin) with hsa
  set H := energy J G with hH
  have hHc : Continuous H := continuous_energy J G hG
  have hexpc : Continuous fun θ : V → Spin => Real.exp (-β * H θ) :=
    Real.continuous_exp.comp (continuous_const.mul hHc)
  have hcosc : Continuous fun θ : V → Spin => Real.Angle.cos (θ o) :=
    Real.Angle.continuous_cos.comp (continuous_apply o)
  set Z : ℝ := ∫ θ, Real.exp (-β * H θ) with hZ
  set C : ℝ := ∫ θ, Real.Angle.cos (θ o) * Real.exp (-β * H θ) with hC
  have hZpos : 0 < Z := partition_pos hG β
  set k : ℝ := Real.exp (β * dirichlet J a / 2) with hk
  have hk1 : 1 ≤ k := by
    rw [hk, show (1:ℝ) = Real.exp 0 by simp]
    refine Real.exp_le_exp.2 ?_
    have := dirichlet_nonneg hJ a
    positivity
  -- shifted values of the observable
  have hsao : sa o = ((Real.pi : ℝ) : Spin) := by rw [hsa]; simp [ho]
  have hshift_sub : ∀ θ : V → Spin, Real.Angle.cos ((θ - sa) o) = -Real.Angle.cos (θ o) := by
    intro θ
    have : (θ - sa) o = θ o - ((Real.pi : ℝ) : Spin) := by
      show θ o - sa o = _; rw [hsao]
    rw [this]; exact Real.Angle.cos_sub_pi _
  have hshift_add : ∀ θ : V → Spin, Real.Angle.cos ((θ + sa) o) = -Real.Angle.cos (θ o) := by
    intro θ
    have : (θ + sa) o = θ o + ((Real.pi : ℝ) : Spin) := by
      show θ o + sa o = _; rw [hsao]
    rw [this]; exact Real.Angle.cos_add_pi _
  -- integrals of `(1 ± cos) * weight`
  have hsplit : ∀ c : ℝ, (∫ θ, (1 + c * Real.Angle.cos (θ o)) * Real.exp (-β * H θ)) = Z + c * C := by
    intro c
    have : ∀ θ : V → Spin, (1 + c * Real.Angle.cos (θ o)) * Real.exp (-β * H θ)
        = Real.exp (-β * H θ) + c * (Real.Angle.cos (θ o) * Real.exp (-β * H θ)) := by
      intro θ; ring
    have hint2 : Integrable
        (fun θ : V → Spin => c * (Real.Angle.cos (θ o) * Real.exp (-β * H θ)))
        (volume : Measure (V → Spin)) :=
      (integrable_of_continuous (hcosc.mul hexpc)).const_mul c
    rw [integral_congr_ae (Filter.Eventually.of_forall this),
      integral_add (integrable_of_continuous hexpc) hint2, integral_const_mul]
  have hkey : ∀ c : ℝ, |c| = 1 → Z + c * C ≤ k * (Z - c * C) := by
    intro c hc
    have hf0 : ∀ θ : V → Spin, 0 ≤ 1 + c * Real.Angle.cos (θ o) := by
      intro θ
      have h1 := angle_abs_cos_le_one (θ o)
      have : |c * Real.Angle.cos (θ o)| ≤ 1 := by
        rw [abs_mul, hc, one_mul]; exact h1
      linarith [(abs_le.mp this).1]
    have hfc : Continuous fun θ : V → Spin => 1 + c * Real.Angle.cos (θ o) :=
      continuous_const.add (continuous_const.mul hcosc)
    have h := gibbs_shift_ineq (a := a) hJ hG hβ hGa
      (fun θ : V → Spin => 1 + c * Real.Angle.cos (θ o)) hf0 hfc
    simp only [← hH, ← hsa] at h
    have e1 : (∫ θ, (1 + c * Real.Angle.cos ((θ - sa) o)) * Real.exp (-β * H θ))
        = Z - c * C := by
      have : ∀ θ : V → Spin, (1 + c * Real.Angle.cos ((θ - sa) o)) * Real.exp (-β * H θ)
          = (1 + (-c) * Real.Angle.cos (θ o)) * Real.exp (-β * H θ) := by
        intro θ; rw [hshift_sub θ]; ring
      rw [integral_congr_ae (Filter.Eventually.of_forall this), hsplit (-c)]; ring
    have e2 : (∫ θ, (1 + c * Real.Angle.cos ((θ + sa) o)) * Real.exp (-β * H θ))
        = Z - c * C := by
      have : ∀ θ : V → Spin, (1 + c * Real.Angle.cos ((θ + sa) o)) * Real.exp (-β * H θ)
          = (1 + (-c) * Real.Angle.cos (θ o)) * Real.exp (-β * H θ) := by
        intro θ; rw [hshift_add θ]; ring
      rw [integral_congr_ae (Filter.Eventually.of_forall this), hsplit (-c)]; ring
    rw [hsplit c, e1, e2] at h
    linarith [h]
  have h1 := hkey 1 (by norm_num)
  have h2 := hkey (-1) (by norm_num)
  have hC1 : C * (k + 1) ≤ Z * (k - 1) := by nlinarith [h1]
  have hC2 : (-C) * (k + 1) ≤ Z * (k - 1) := by nlinarith [h2]
  have habs : |C| * (k + 1) ≤ Z * (k - 1) := by
    rcases abs_cases C with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> assumption
  have heq : |gibbsAvg β H fun θ => Real.Angle.cos (θ o)| = |C| / Z := by
    rw [gibbsAvg, abs_div, abs_of_pos hZpos]
  rw [heq, div_le_iff₀ hZpos]
  nlinarith [habs, abs_nonneg C, mul_nonneg (abs_nonneg C) (sub_nonneg.2 hk1), hZpos.le]

end Phys

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

import RequestProject.Core
import RequestProject.Capacity

/-!
# The nearest-neighbour rotator model on a finite box of `ℤ^d`

We combine the abstract Mermin–Wagner bound of `Core` with the capacity estimate of
`Capacity`: for `d ≤ 2` the Dirichlet energy of the logarithmic spin-wave profile tends
to `0`, uniformly in the size of the box.
-/

open Finset MeasureTheory

namespace Phys

/-- The sites of the box of side `2N+1`, as a type. -/
abbrev Site (d N : ℕ) := {x : Fin d → ℤ // x ∈ box d N}

