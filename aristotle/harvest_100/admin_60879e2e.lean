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

/-- The spatial partial derivative of a space-time function `h : ℝ → ℝ → ℝ`
(first argument = time, second argument = space). -/
noncomputable def dx (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => deriv (fun y => h t y) x

/-- The time partial derivative of a space-time function `h : ℝ → ℝ → ℝ`. -/
noncomputable def dt (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => deriv (fun s => h s x) t

/-- The (deterministic) KPZ equation `∂ₜ h = ∂ₓₓ h + (∂ₓ h)²`. -/
def IsKPZSolution (h : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, dt h t x = dx (dx h) t x + (dx h t x) ^ 2

/-- The heat equation `∂ₜ Z = ∂ₓₓ Z`. -/
def IsHeatSolution (Z : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, dt Z t x = dx (dx Z) t x

/-- Smoothness assumptions used throughout: `h` is differentiable in time for each
fixed space point, and twice differentiable in space for each fixed time. -/
structure Regular (h : ℝ → ℝ → ℝ) : Prop where
  time : ∀ x : ℝ, Differentiable ℝ (fun t => h t x)
  space : ∀ t : ℝ, Differentiable ℝ (fun y => h t y)
  space2 : ∀ t : ℝ, Differentiable ℝ (fun y => dx h t y)

section ColeHopf

variable {h : ℝ → ℝ → ℝ}

/-- The Cole–Hopf transform `Z = exp h`. -/
noncomputable def coleHopf (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => Real.exp (h t x)

lemma hasDerivAt_space (H : Regular h) (t x : ℝ) :
    HasDerivAt (fun y => h t y) (dx h t x) x :=
  (H.space t x).hasDerivAt

lemma hasDerivAt_time (H : Regular h) (t x : ℝ) :
    HasDerivAt (fun s => h s x) (dt h t x) t :=
  (H.time x t).hasDerivAt

lemma hasDerivAt_space2 (H : Regular h) (t x : ℝ) :
    HasDerivAt (fun y => dx h t y) (dx (dx h) t x) x :=
  (H.space2 t x).hasDerivAt

/-- Spatial derivative of the Cole–Hopf transform. -/
lemma dx_coleHopf (H : Regular h) (t x : ℝ) :
    dx (coleHopf h) t x = Real.exp (h t x) * dx h t x :=
  ((hasDerivAt_space H t x).exp).deriv

/-- Second spatial derivative of the Cole–Hopf transform. -/
lemma dx_dx_coleHopf (H : Regular h) (t x : ℝ) :
    dx (dx (coleHopf h)) t x
      = Real.exp (h t x) * ((dx h t x) ^ 2 + dx (dx h) t x) := by
  have hfun : (fun y => dx (coleHopf h) t y)
      = fun y => Real.exp (h t y) * dx h t y := by
    funext y; exact dx_coleHopf H t y
  have hd : HasDerivAt (fun y => Real.exp (h t y) * dx h t y)
      (Real.exp (h t x) * dx h t x * dx h t x
        + Real.exp (h t x) * dx (dx h) t x) x :=
    ((hasDerivAt_space H t x).exp).mul (hasDerivAt_space2 H t x)
  have key : dx (dx (coleHopf h)) t x
      = deriv (fun y => Real.exp (h t y) * dx h t y) x :=
    congrArg (fun f => deriv f x) hfun
  rw [key, hd.deriv]; ring

/-- Time derivative of the Cole–Hopf transform. -/
lemma dt_coleHopf (H : Regular h) (t x : ℝ) :
    dt (coleHopf h) t x = Real.exp (h t x) * dt h t x :=
  ((hasDerivAt_time H t x).exp).deriv

end ColeHopf

/-- **Hairer KPZ (Cole–Hopf reduction).**

For sufficiently regular space-time functions, the (deterministic) KPZ equation
`∂ₜ h = ∂ₓₓ h + (∂ₓ h)²` is *equivalent*, under the Cole–Hopf transformation
`Z = exp h`, to the linear heat equation `∂ₜ Z = ∂ₓₓ Z`.

This is the classical reduction underlying the well-posedness theory of the KPZ
equation: it identifies solutions of the nonlinear KPZ equation with (positive)
solutions of the linear heat equation, for which existence and uniqueness are
classical.  Hairer's theory of regularity structures extends this to the
stochastic setting; here we formalize and prove the deterministic base case. -/
theorem hairer_KPZ {h : ℝ → ℝ → ℝ} (H : Regular h) :
    IsKPZSolution h ↔ IsHeatSolution (coleHopf h) := by
  constructor
  · intro hk t x
    rw [dt_coleHopf H, dx_dx_coleHopf H, hk t x]
    ring
  · intro hz t x
    have h1 := hz t x
    rw [dt_coleHopf H, dx_dx_coleHopf H] at h1
    have hpos : Real.exp (h t x) ≠ 0 := (Real.exp_pos _).ne'
    have := mul_left_cancel₀ hpos h1
    rw [this]; ring

section LogTransform

variable {Z : ℝ → ℝ → ℝ}

/-- Spatial derivative of `log Z` for a positive function `Z`. -/
lemma dx_log (HZ : Regular Z) (hpos : ∀ t x, 0 < Z t x) (t x : ℝ) :
    dx (fun t x => Real.log (Z t x)) t x = dx Z t x / Z t x :=
  ((hasDerivAt_space HZ t x).log (hpos t x).ne').deriv

/-- `log Z` is regular whenever `Z` is regular and positive. -/
lemma regular_log (HZ : Regular Z) (hpos : ∀ t x, 0 < Z t x) :
    Regular (fun t x => Real.log (Z t x)) where
  time := fun x => (HZ.time x).log (fun t => (hpos t x).ne')
  space := fun t => (HZ.space t).log (fun x => (hpos t x).ne')
  space2 := fun t => by
    have hfun : (fun y => dx (fun t x => Real.log (Z t x)) t y)
        = fun y => dx Z t y / Z t y := by
      funext y; exact dx_log HZ hpos t y
    rw [hfun]
    exact (HZ.space2 t).div (HZ.space t) (fun y => (hpos t y).ne')

/-- The Cole–Hopf transform inverts the logarithm on positive functions. -/
lemma coleHopf_log (hpos : ∀ t x, 0 < Z t x) :
    coleHopf (fun t x => Real.log (Z t x)) = Z := by
  funext t x
  exact Real.exp_log (hpos t x)

/-- **Hairer KPZ, inverse Cole–Hopf direction.**

A positive regular solution of the heat equation yields, via `h = log Z`,
a solution of the KPZ equation, and conversely. -/
theorem hairer_KPZ_log (HZ : Regular Z) (hpos : ∀ t x, 0 < Z t x) :
    IsHeatSolution Z ↔ IsKPZSolution (fun t x => Real.log (Z t x)) := by
  have h := hairer_KPZ (regular_log HZ hpos)
  rw [coleHopf_log hpos] at h
  exact h.symm

end LogTransform

end Frontier

