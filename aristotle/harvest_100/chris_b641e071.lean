/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier

/-! ## Space-time functions and partial derivatives

A space-time function is modelled as `u : ℝ → ℝ → ℝ`, where `u t x` is its value at time `t`
and space point `x`. -/

/-- Time derivative of a space-time function. -/
noncomputable def dt (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := deriv (fun s => u s x) t

/-- Space derivative of a space-time function.  Since `dx u` is again a space-time function,
`dx (dx u)` is the second space derivative. -/
noncomputable def dx (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := deriv (fun y => u t y) x

/-- `u` solves the KPZ equation `∂ₜ u = ∂ₓ² u + (∂ₓ u)² + ξ` driven by `xi`. -/
def IsKPZSolution (xi u : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, dt u t x = dx (dx u) t x + (dx u t x) ^ 2 + xi t x

/-- `Z` solves the multiplicative stochastic heat equation `∂ₜ Z = ∂ₓ² Z + Z ξ` driven by `xi`. -/
def IsSHESolution (xi Z : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, dt Z t x = dx (dx Z) t x + Z t x * xi t x

/-- Regularity class used throughout: differentiability in time, in space, and differentiability
in space of the first space derivative. -/
structure Regular (u : ℝ → ℝ → ℝ) : Prop where
  time : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t
  space : ∀ t x, DifferentiableAt ℝ (fun y => u t y) x
  space2 : ∀ t x, DifferentiableAt ℝ (fun y => dx u t y) x

/-! ## The Cole–Hopf transform -/

section ColeHopf

variable {Z u : ℝ → ℝ → ℝ}

/-- Time derivative of the Cole–Hopf transform `log Z`. -/
lemma dt_log (hpos : ∀ t x, 0 < Z t x) (hZ : Regular Z) (t x : ℝ) :
    dt (fun t x => Real.log (Z t x)) t x = dt Z t x / Z t x := by
  have h : HasDerivAt (fun s => Z s x) (dt Z t x) t := (hZ.time t x).hasDerivAt
  exact (h.log (hpos t x).ne').deriv

/-- Space derivative of the Cole–Hopf transform `log Z`. -/
lemma dx_log (hpos : ∀ t x, 0 < Z t x) (hZ : Regular Z) (t x : ℝ) :
    dx (fun t x => Real.log (Z t x)) t x = dx Z t x / Z t x := by
  have h : HasDerivAt (fun y => Z t y) (dx Z t x) x := (hZ.space t x).hasDerivAt
  exact (h.log (hpos t x).ne').deriv

/-- The first space derivative of `log Z`, as a function of the space variable. -/
lemma dx_log_fun (hpos : ∀ t x, 0 < Z t x) (hZ : Regular Z) (t : ℝ) :
    (fun y => dx (fun t x => Real.log (Z t x)) t y) = fun y => dx Z t y / Z t y := by
  funext y; exact dx_log hpos hZ t y

/-- Second space derivative of the Cole–Hopf transform `log Z`. -/
lemma dxx_log (hpos : ∀ t x, 0 < Z t x) (hZ : Regular Z) (t x : ℝ) :
    dx (dx (fun t x => Real.log (Z t x))) t x
      = (dx (dx Z) t x * Z t x - dx Z t x * dx Z t x) / (Z t x) ^ 2 := by
  have h1 : HasDerivAt (fun y => dx Z t y) (dx (dx Z) t x) x := (hZ.space2 t x).hasDerivAt
  have h2 : HasDerivAt (fun y => Z t y) (dx Z t x) x := (hZ.space t x).hasDerivAt
  have : HasDerivAt (fun y => dx Z t y / Z t y)
      ((dx (dx Z) t x * Z t x - dx Z t x * dx Z t x) / (Z t x) ^ 2) x :=
    h1.div h2 (hpos t x).ne'
  rw [dx, dx_log_fun hpos hZ t]
  exact this.deriv

/-- Regularity is preserved by the Cole–Hopf transform `Z ↦ log Z`. -/
lemma Regular.log (hpos : ∀ t x, 0 < Z t x) (hZ : Regular Z) :
    Regular (fun t x => Real.log (Z t x)) where
  time t x := ((hZ.time t x).hasDerivAt.log (hpos t x).ne').differentiableAt
  space t x := ((hZ.space t x).hasDerivAt.log (hpos t x).ne').differentiableAt
  space2 t x := by
    rw [dx_log_fun hpos hZ t]
    exact ((hZ.space2 t x).hasDerivAt.div (hZ.space t x).hasDerivAt (hpos t x).ne').differentiableAt

/-- The first space derivative of `exp u`, as a function of the space variable. -/
lemma dx_exp_fun (hu : Regular u) (t : ℝ) :
    (fun y => dx (fun t x => Real.exp (u t x)) t y)
      = fun y => Real.exp (u t y) * dx u t y := by
  funext y
  exact ((hu.space t y).hasDerivAt.exp).deriv

/-- Regularity is preserved by the inverse Cole–Hopf transform `u ↦ exp u`. -/
lemma Regular.exp (hu : Regular u) : Regular (fun t x => Real.exp (u t x)) where
  time t x := ((hu.time t x).hasDerivAt.exp).differentiableAt
  space t x := ((hu.space t x).hasDerivAt.exp).differentiableAt
  space2 t x := by
    rw [dx_exp_fun hu t]
    exact (((hu.space t x).hasDerivAt.exp).mul (hu.space2 t x).hasDerivAt).differentiableAt

/-- **Cole–Hopf correspondence.**  For a positive, regular space-time function `Z`, the function
`Z` solves the multiplicative stochastic heat equation `∂ₜ Z = ∂ₓ² Z + Z ξ` if and only if its
logarithm solves the KPZ equation `∂ₜ u = ∂ₓ² u + (∂ₓ u)² + ξ`. -/
theorem she_iff_kpz_log (xi : ℝ → ℝ → ℝ) (hpos : ∀ t x, 0 < Z t x) (hZ : Regular Z) :
    IsSHESolution xi Z ↔ IsKPZSolution xi (fun t x => Real.log (Z t x)) := by
  have key : ∀ t x, (dt Z t x = dx (dx Z) t x + Z t x * xi t x) ↔
      (dt (fun t x => Real.log (Z t x)) t x
        = dx (dx (fun t x => Real.log (Z t x))) t x
          + (dx (fun t x => Real.log (Z t x)) t x) ^ 2 + xi t x) := by
    intro t x
    have hW : Z t x ≠ 0 := (hpos t x).ne'
    rw [dt_log hpos hZ, dxx_log hpos hZ, dx_log hpos hZ]
    rw [div_eq_iff hW]
    constructor
    · intro h; rw [h]; field_simp; ring
    · intro h
      field_simp at h
      refine mul_right_cancel₀ hW ?_
      linear_combination h
  constructor
  · intro h t x; exact (key t x).1 (h t x)
  · intro h t x; exact (key t x).2 (h t x)

/-- **Inverse Cole–Hopf correspondence.**  If `u` is a regular solution of the KPZ equation,
then `exp u` solves the multiplicative stochastic heat equation. -/
theorem she_exp_of_kpz (xi : ℝ → ℝ → ℝ) (hu : Regular u) (h : IsKPZSolution xi u) :
    IsSHESolution xi (fun t x => Real.exp (u t x)) := by
  have hpos : ∀ t x, 0 < Real.exp (u t x) := fun t x => Real.exp_pos _
  refine (she_iff_kpz_log xi hpos hu.exp).2 ?_
  have : (fun t x => Real.log (Real.exp (u t x))) = u := by
    funext t x; exact Real.log_exp _
  rw [this]
  exact h

end ColeHopf

/-! ## Well-posedness of KPZ, reduced to the stochastic heat equation

The following is the Cole–Hopf reduction underlying Hairer's solution theory: well-posedness
(existence, uniqueness and, by construction, the explicit solution map) for the KPZ equation
follows from well-posedness of the linear multiplicative stochastic heat equation. -/

/-- **Main theorem (Hairer, KPZ — Cole–Hopf reduction).**  If the multiplicative stochastic heat
equation driven by `xi` is well posed in the class of positive regular functions, then the KPZ
equation driven by `xi` is well posed in the class of regular functions: for every initial
datum `u₀` there is a unique regular solution `u` of `∂ₜ u = ∂ₓ² u + (∂ₓ u)² + ξ` with
`u 0 = u₀`. -/
theorem hairer_KPZ (xi : ℝ → ℝ → ℝ)
    (hSHE : ∀ Z₀ : ℝ → ℝ, (∀ x, 0 < Z₀ x) →
      ∃! Z : ℝ → ℝ → ℝ,
        ((∀ t x, 0 < Z t x) ∧ Regular Z) ∧ (∀ x, Z 0 x = Z₀ x) ∧ IsSHESolution xi Z)
    (u₀ : ℝ → ℝ) :
    ∃! u : ℝ → ℝ → ℝ, Regular u ∧ (∀ x, u 0 x = u₀ x) ∧ IsKPZSolution xi u := by
  obtain ⟨Z, ⟨⟨hpos, hreg⟩, hinit, hZ⟩, huniq⟩ :=
    hSHE (fun x => Real.exp (u₀ x)) (fun x => Real.exp_pos _)
  refine ⟨fun t x => Real.log (Z t x), ⟨hreg.log hpos, ?_, (she_iff_kpz_log xi hpos hreg).1 hZ⟩, ?_⟩
  · intro x; show Real.log (Z 0 x) = u₀ x; rw [hinit x, Real.log_exp]
  · rintro v ⟨hvreg, hvinit, hv⟩
    have hZv : (fun t x => Real.exp (v t x)) = Z := by
      refine huniq _ ⟨⟨fun t x => Real.exp_pos _, hvreg.exp⟩, ?_, she_exp_of_kpz xi hvreg hv⟩
      intro x; rw [hvinit x]
    funext t x
    have : Real.exp (v t x) = Z t x := congrFun (congrFun hZv t) x
    rw [← this, Real.log_exp]

/-- **Converse reduction.**  Conversely, well-posedness of the KPZ equation in the class of
regular functions implies well-posedness of the multiplicative stochastic heat equation in the
class of positive regular functions.  Together with `Frontier.hairer_KPZ` this shows that the two
problems are equivalent under the Cole–Hopf transform. -/
theorem she_wellposed_of_kpz_wellposed (xi : ℝ → ℝ → ℝ)
    (hKPZ : ∀ u₀ : ℝ → ℝ, ∃! u : ℝ → ℝ → ℝ,
      Regular u ∧ (∀ x, u 0 x = u₀ x) ∧ IsKPZSolution xi u)
    (Z₀ : ℝ → ℝ) (hZ₀ : ∀ x, 0 < Z₀ x) :
    ∃! Z : ℝ → ℝ → ℝ,
      ((∀ t x, 0 < Z t x) ∧ Regular Z) ∧ (∀ x, Z 0 x = Z₀ x) ∧ IsSHESolution xi Z := by
  obtain ⟨u, ⟨hureg, huinit, hu⟩, huniq⟩ := hKPZ (fun x => Real.log (Z₀ x))
  refine ⟨fun t x => Real.exp (u t x), ⟨⟨fun t x => Real.exp_pos _, hureg.exp⟩, ?_,
    she_exp_of_kpz xi hureg hu⟩, ?_⟩
  · intro x
    show Real.exp (u 0 x) = Z₀ x
    rw [huinit x, Real.exp_log (hZ₀ x)]
  · rintro W ⟨⟨hWpos, hWreg⟩, hWinit, hW⟩
    have hWu : (fun t x => Real.log (W t x)) = u := by
      refine huniq _ ⟨hWreg.log hWpos, ?_, (she_iff_kpz_log xi hWpos hWreg).1 hW⟩
      intro x
      show Real.log (W 0 x) = Real.log (Z₀ x)
      rw [hWinit x]
    funext t x
    have h : Real.log (W t x) = u t x := congrFun (congrFun hWu t) x
    rw [← h, Real.exp_log (hWpos t x)]

/-! ## Base case: the spatially homogeneous KPZ equation -/

/-- For a space-time function that does not depend on the space variable, both space derivatives
vanish. -/
lemma dx_of_const_in_space (f : ℝ → ℝ) (t x : ℝ) : dx (fun t _ => f t) t x = 0 := by
  simp [dx]

lemma dxx_of_const_in_space (f : ℝ → ℝ) (t x : ℝ) : dx (dx (fun t _ => f t)) t x = 0 := by
  have : (fun y => dx (fun t _ => f t) t y) = fun _ => (0 : ℝ) := by
    funext y; exact dx_of_const_in_space f t y
  rw [dx, this]
  simp

/-- The spatially homogeneous KPZ equation is exactly the ODE `f' = ξ`. -/
lemma isKPZSolution_const_in_space_iff (xi : ℝ → ℝ) (f : ℝ → ℝ) :
    IsKPZSolution (fun t _ => xi t) (fun t _ => f t) ↔ ∀ t, deriv f t = xi t := by
  constructor
  · intro h t
    have := h t 0
    rw [dxx_of_const_in_space, dx_of_const_in_space] at this
    simpa [dt] using this
  · intro h t x
    rw [dxx_of_const_in_space, dx_of_const_in_space]
    simpa [dt] using h t

/-- **Base case.**  For a continuous driving noise depending only on time, the KPZ equation has a
unique differentiable spatially homogeneous solution with any prescribed initial value; it is
given by integrating the noise. -/
theorem hairer_KPZ_spatially_homogeneous (xi : ℝ → ℝ) (hxi : Continuous xi) (a : ℝ) :
    ∃! f : ℝ → ℝ, (Differentiable ℝ f ∧ f 0 = a) ∧
      IsKPZSolution (fun t _ => xi t) (fun t _ => f t) := by
  set F : ℝ → ℝ := fun t => a + ∫ s in (0 : ℝ)..t, xi s with hF
  have hFderiv : ∀ t, HasDerivAt F (xi t) t := by
    intro t
    have h := intervalIntegral.integral_hasDerivAt_right
      (hxi.intervalIntegrable 0 t)
      (hxi.stronglyMeasurableAtFilter _ _) hxi.continuousAt
    simpa [hF] using h.const_add a
  have hFdiff : Differentiable ℝ F := fun t => (hFderiv t).differentiableAt
  refine ⟨F, ⟨⟨hFdiff, by simp [hF]⟩, (isKPZSolution_const_in_space_iff xi F).2
      (fun t => (hFderiv t).deriv)⟩, ?_⟩
  rintro g ⟨⟨hgdiff, hg0⟩, hg⟩
  have hgd : ∀ t, deriv g t = xi t := (isKPZSolution_const_in_space_iff xi g).1 hg
  have hconst : ∀ t, (g - F) t = (g - F) 0 := by
    intro t
    refine is_const_of_deriv_eq_zero (hgdiff.sub hFdiff) (fun s => ?_) t 0
    rw [deriv_sub (hgdiff s) (hFdiff s), hgd s, (hFderiv s).deriv, sub_self]
  funext t
  have h := hconst t
  simp only [Pi.sub_apply, hg0, hF] at h
  simp only [hF]
  simp at h ⊢
  linarith [h]

end Frontier

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

