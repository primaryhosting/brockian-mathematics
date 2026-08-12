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

/-! ## Space-time partial derivatives

We work with real functions `f : ℝ → ℝ → ℝ` of a time variable and a (one dimensional)
space variable. -/

/-- Partial derivative in the time variable. -/
noncomputable def dt (f : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := deriv (fun s : ℝ => f s x) t

/-- Partial derivative in the space variable. -/
noncomputable def dx (f : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := deriv (fun y : ℝ => f t y) x

/-- Minimal regularity needed to make sense of the equations below classically:
differentiability in time, and twice differentiability in space. -/
structure SpaceTimeReg (f : ℝ → ℝ → ℝ) : Prop where
  time : ∀ t x : ℝ, DifferentiableAt ℝ (fun s : ℝ => f s x) t
  space : ∀ t x : ℝ, DifferentiableAt ℝ (fun y : ℝ => f t y) x
  space2 : ∀ t x : ℝ, DifferentiableAt ℝ (fun y : ℝ => dx f t y) x

/-- `Z` is a (classical) solution of the multiplicative stochastic heat equation
`∂_t Z = ∂_x² Z + Z ξ` driven by `ξ`. -/
def IsSHESolution (xi Z : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x : ℝ, dt Z t x = dx (dx Z) t x + Z t x * xi t x

/-- `h` is a (classical) solution of the KPZ equation
`∂_t h = ∂_x² h + (∂_x h)² + ξ` driven by `ξ`. -/
def IsKPZSolution (xi h : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x : ℝ, dt h t x = dx (dx h) t x + (dx h t x) ^ 2 + xi t x

/-! ## Elementary derivative computations -/

theorem dx_apply (f : ℝ → ℝ → ℝ) (t x : ℝ) : dx f t x = deriv (fun y : ℝ => f t y) x := rfl

theorem dt_apply (f : ℝ → ℝ → ℝ) (t x : ℝ) : dt f t x = deriv (fun s : ℝ => f s x) t := rfl

/-- The space derivative of `log Z`. -/
theorem dx_log (Z : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg Z) (hpos : ∀ t x : ℝ, 0 < Z t x)
    (t x : ℝ) : dx (fun t x => Real.log (Z t x)) t x = dx Z t x / Z t x :=
  (((hreg.space t x).hasDerivAt).log (ne_of_gt (hpos t x))).deriv

/-- The time derivative of `log Z`. -/
theorem dt_log (Z : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg Z) (hpos : ∀ t x : ℝ, 0 < Z t x)
    (t x : ℝ) : dt (fun t x => Real.log (Z t x)) t x = dt Z t x / Z t x :=
  (((hreg.time t x).hasDerivAt).log (ne_of_gt (hpos t x))).deriv

/-- The second space derivative of `log Z`. -/
theorem dx_dx_log (Z : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg Z) (hpos : ∀ t x : ℝ, 0 < Z t x)
    (t x : ℝ) :
    dx (dx (fun t x => Real.log (Z t x))) t x
      = dx (dx Z) t x / Z t x - (dx Z t x / Z t x) ^ 2 := by
  have key : (fun y : ℝ => dx (fun t x => Real.log (Z t x)) t y)
      = fun y : ℝ => dx Z t y / Z t y := by
    funext y
    exact dx_log Z hreg hpos t y
  have hu : HasDerivAt (fun y : ℝ => dx Z t y) (dx (dx Z) t x) x := (hreg.space2 t x).hasDerivAt
  have hv : HasDerivAt (fun y : ℝ => Z t y) (dx Z t x) x := (hreg.space t x).hasDerivAt
  have hne : Z t x ≠ 0 := ne_of_gt (hpos t x)
  have hdiv : HasDerivAt (fun y : ℝ => dx Z t y / Z t y)
      ((dx (dx Z) t x * Z t x - dx Z t x * dx Z t x) / Z t x ^ 2) x := hu.div hv hne
  rw [dx_apply, key, hdiv.deriv]
  field_simp

/-- The space derivative of `exp h`. -/
theorem dx_exp (h : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg h) (t x : ℝ) :
    dx (fun t x => Real.exp (h t x)) t x = Real.exp (h t x) * dx h t x :=
  (((hreg.space t x).hasDerivAt).exp).deriv

/-- The time derivative of `exp h`. -/
theorem dt_exp (h : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg h) (t x : ℝ) :
    dt (fun t x => Real.exp (h t x)) t x = Real.exp (h t x) * dt h t x :=
  (((hreg.time t x).hasDerivAt).exp).deriv

/-- The second space derivative of `exp h`. -/
theorem dx_dx_exp (h : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg h) (t x : ℝ) :
    dx (dx (fun t x => Real.exp (h t x))) t x
      = Real.exp (h t x) * (dx (dx h) t x + (dx h t x) ^ 2) := by
  have key : (fun y : ℝ => dx (fun t x => Real.exp (h t x)) t y)
      = fun y : ℝ => Real.exp (h t y) * dx h t y := by
    funext y
    exact dx_exp h hreg t y
  have hu : HasDerivAt (fun y : ℝ => Real.exp (h t y)) (Real.exp (h t x) * dx h t x) x :=
    ((hreg.space t x).hasDerivAt).exp
  have hv : HasDerivAt (fun y : ℝ => dx h t y) (dx (dx h) t x) x := (hreg.space2 t x).hasDerivAt
  have hmul : HasDerivAt (fun y : ℝ => Real.exp (h t y) * dx h t y)
      (Real.exp (h t x) * dx h t x * dx h t x + Real.exp (h t x) * dx (dx h) t x) x := hu.mul hv
  rw [dx_apply, key, hmul.deriv]
  ring

/-! ## Regularity is preserved by the Cole–Hopf transform -/

theorem SpaceTimeReg.log (Z : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg Z) (hpos : ∀ t x : ℝ, 0 < Z t x) :
    SpaceTimeReg (fun t x => Real.log (Z t x)) where
  time t x := (hreg.time t x).log (ne_of_gt (hpos t x))
  space t x := (hreg.space t x).log (ne_of_gt (hpos t x))
  space2 t x := by
    have key : (fun y : ℝ => dx (fun t x => Real.log (Z t x)) t y)
        = fun y : ℝ => dx Z t y / Z t y := by
      funext y
      exact dx_log Z hreg hpos t y
    rw [key]
    exact (hreg.space2 t x).div (hreg.space t x) (ne_of_gt (hpos t x))

theorem SpaceTimeReg.exp (h : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg h) :
    SpaceTimeReg (fun t x => Real.exp (h t x)) where
  time t x := (hreg.time t x).exp
  space t x := (hreg.space t x).exp
  space2 t x := by
    have key : (fun y : ℝ => dx (fun t x => Real.exp (h t x)) t y)
        = fun y : ℝ => Real.exp (h t y) * dx h t y := by
      funext y
      exact dx_exp h hreg t y
    rw [key]
    exact ((hreg.space t x).exp).mul (hreg.space2 t x)

/-! ## The Cole–Hopf reduction -/

/-- **Cole–Hopf, forward direction.** If `Z > 0` solves the multiplicative stochastic heat
equation with noise `ξ`, then `h = log Z` solves the KPZ equation with the same noise. -/
theorem isKPZSolution_log (xi Z : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg Z)
    (hpos : ∀ t x : ℝ, 0 < Z t x) (hZ : IsSHESolution xi Z) :
    IsKPZSolution xi (fun t x => Real.log (Z t x)) := by
  intro t x
  have hne : Z t x ≠ 0 := ne_of_gt (hpos t x)
  rw [dt_log Z hreg hpos, dx_dx_log Z hreg hpos, dx_log Z hreg hpos, hZ t x]
  field_simp
  ring

/-- **Cole–Hopf, backward direction.** If `h` solves the KPZ equation with noise `ξ`, then
`Z = exp h` is a positive solution of the multiplicative stochastic heat equation with the
same noise. -/
theorem isSHESolution_exp (xi h : ℝ → ℝ → ℝ) (hreg : SpaceTimeReg h)
    (hh : IsKPZSolution xi h) :
    IsSHESolution xi (fun t x => Real.exp (h t x)) := by
  intro t x
  rw [dt_exp h hreg, dx_dx_exp h hreg, hh t x]
  ring

/-! ## The base case: explicit solutions -/

/-- **Base case.** For a continuous, spatially homogeneous noise `ξ (t, x) = g t` and any slope
`a`, the function `h (t, x) = a x + a² t + ∫₀ᵗ g` is a classical solution of the KPZ equation. -/
theorem isKPZSolution_explicit (g : ℝ → ℝ) (hg : Continuous g) (a : ℝ) :
    SpaceTimeReg (fun t x => a * x + a ^ 2 * t + ∫ s in (0 : ℝ)..t, g s) ∧
      IsKPZSolution (fun t _ => g t)
        (fun t x => a * x + a ^ 2 * t + ∫ s in (0 : ℝ)..t, g s) := by
  set h : ℝ → ℝ → ℝ := fun t x => a * x + a ^ 2 * t + ∫ s in (0 : ℝ)..t, g s with hh
  have hI : ∀ u : ℝ, HasDerivAt (fun v : ℝ => ∫ s in (0 : ℝ)..v, g s) (g u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 u)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  have htime : ∀ t x : ℝ, HasDerivAt (fun s : ℝ => h s x) (a ^ 2 + g t) t := by
    intro t x
    have : HasDerivAt (fun s : ℝ => a * x + (a ^ 2 * s + ∫ u in (0 : ℝ)..s, g u))
        (0 + (a ^ 2 * 1 + g t)) t :=
      (hasDerivAt_const t (a * x)).add (((hasDerivAt_id t).const_mul (a ^ 2)).add (hI t))
    simpa [hh, add_assoc] using this
  have hspace : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => h t y) a x := by
    intro t x
    have : HasDerivAt (fun y : ℝ => a * y + (a ^ 2 * t + ∫ u in (0 : ℝ)..t, g u)) (a * 1 + 0) x :=
      ((hasDerivAt_id x).const_mul a).add (hasDerivAt_const x _)
    simpa [hh, add_assoc] using this
  have hdx : ∀ t x : ℝ, dx h t x = a := fun t x => (hspace t x).deriv
  have hreg : SpaceTimeReg h := by
    refine ⟨fun t x => (htime t x).differentiableAt, fun t x => (hspace t x).differentiableAt,
      fun t x => ?_⟩
    have key : (fun y : ℝ => dx h t y) = fun _ : ℝ => a := by
      funext y; exact hdx t y
    rw [key]
    exact differentiableAt_const a
  refine ⟨hreg, ?_⟩
  intro t x
  have hdxdx : dx (dx h) t x = 0 := by
    have key : (fun y : ℝ => dx h t y) = fun _ : ℝ => a := by
      funext y; exact hdx t y
    rw [dx_apply, key, deriv_const]
  rw [dt_apply, (htime t x).deriv, hdxdx, hdx t x]
  ring

/-! ## The base case: the fundamental solution of the linear equation -/

/-- The heat kernel `(4πt)^(-1/2) exp (-x²/(4t))` for `t > 0`, extended by `0` for `t ≤ 0`. -/
noncomputable def heatKernel (t x : ℝ) : ℝ :=
  if 0 < t then Real.exp (-(1 / 2) * Real.log (4 * Real.pi * t) - x ^ 2 / (4 * t)) else 0

theorem heatKernel_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heatKernel t x := by
  rw [heatKernel, if_pos ht]
  exact Real.exp_pos _

/-- The heat kernel is given by the familiar Gaussian formula. -/
theorem heatKernel_eq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatKernel t x = Real.exp (-(x ^ 2) / (4 * t)) / Real.sqrt (4 * Real.pi * t) := by
  have hA : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hsqrt : Real.sqrt (4 * Real.pi * t) = Real.exp (Real.log (4 * Real.pi * t) / 2) := by
    rw [← Real.log_sqrt hA.le, Real.exp_log (Real.sqrt_pos.mpr hA)]
  rw [heatKernel, if_pos ht, hsqrt, ← Real.exp_sub]
  ring_nf

theorem hasDerivAt_heatKernel_space {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun z : ℝ => heatKernel t z) (heatKernel t y * (-(y / (2 * t)))) y := by
  have hfun : (fun z : ℝ => heatKernel t z)
      = fun z : ℝ => Real.exp (-(1 / 2) * Real.log (4 * Real.pi * t) - z ^ 2 / (4 * t)) := by
    funext z
    rw [heatKernel, if_pos ht]
  have hval : heatKernel t y
      = Real.exp (-(1 / 2) * Real.log (4 * Real.pi * t) - y ^ 2 / (4 * t)) := by
    rw [heatKernel, if_pos ht]
  have htne : t ≠ 0 := ne_of_gt ht
  have hinner : HasDerivAt
      (fun z : ℝ => -(1 / 2) * Real.log (4 * Real.pi * t) - z ^ 2 / (4 * t))
      (-(y / (2 * t))) y := by
    have h1 : HasDerivAt (fun z : ℝ => z ^ 2 / (4 * t)) ((2 : ℕ) * y ^ (2 - 1) / (4 * t)) y :=
      (hasDerivAt_pow 2 y).div_const (4 * t)
    have h2 := h1.const_sub (-(1 / 2) * Real.log (4 * Real.pi * t))
    convert h2 using 1
    field_simp
    ring
  rw [hfun, hval]
  exact hinner.exp

theorem dx_heatKernel {t : ℝ} (ht : 0 < t) (y : ℝ) :
    dx heatKernel t y = heatKernel t y * (-(y / (2 * t))) :=
  (hasDerivAt_heatKernel_space ht y).deriv

theorem dx_dx_heatKernel {t : ℝ} (ht : 0 < t) (x : ℝ) :
    dx (dx heatKernel) t x = heatKernel t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
  have key : (fun y : ℝ => dx heatKernel t y)
      = fun y : ℝ => heatKernel t y * (-(y / (2 * t))) := by
    funext y
    exact dx_heatKernel ht y
  have hu := hasDerivAt_heatKernel_space ht x
  have hv : HasDerivAt (fun y : ℝ => -(y / (2 * t))) (-(1 / (2 * t))) x := by
    simpa using ((hasDerivAt_id x).div_const (2 * t)).neg
  have hmul : HasDerivAt (fun y : ℝ => heatKernel t y * -(y / (2 * t)))
      (heatKernel t x * -(x / (2 * t)) * -(x / (2 * t)) + heatKernel t x * -(1 / (2 * t))) x :=
    hu.mul hv
  have htne : t ≠ 0 := ne_of_gt ht
  rw [dx_apply, key, hmul.deriv]
  field_simp
  ring

theorem dt_heatKernel {t : ℝ} (ht : 0 < t) (x : ℝ) :
    dt heatKernel t x = heatKernel t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
  have htne : t ≠ 0 := ne_of_gt ht
  have hpi : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hlog : HasDerivAt (fun s : ℝ => Real.log (4 * Real.pi * s))
      (4 * Real.pi * 1 / (4 * Real.pi * t)) t :=
    ((hasDerivAt_id t).const_mul (4 * Real.pi)).log (ne_of_gt hpi)
  have hquot : HasDerivAt (fun s : ℝ => x ^ 2 / (4 * s))
      ((0 * (4 * t) - x ^ 2 * (4 * 1)) / (4 * t) ^ 2) t :=
    (hasDerivAt_const t (x ^ 2)).div ((hasDerivAt_id t).const_mul 4) (by positivity)
  have hinner : HasDerivAt
      (fun s : ℝ => -(1 / 2) * Real.log (4 * Real.pi * s) - x ^ 2 / (4 * s))
      (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) t := by
    have h := (hlog.const_mul (-(1 / 2) : ℝ)).sub hquot
    convert h using 1
    have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  have hev : (fun s : ℝ => heatKernel s x) =ᶠ[nhds t]
      fun s : ℝ => Real.exp (-(1 / 2) * Real.log (4 * Real.pi * s) - x ^ 2 / (4 * s)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Set.Ioi (0 : ℝ) from ht)] with s hs
    rw [heatKernel, if_pos (Set.mem_Ioi.mp hs)]
  have hval : heatKernel t x
      = Real.exp (-(1 / 2) * Real.log (4 * Real.pi * t) - x ^ 2 / (4 * t)) := by
    rw [heatKernel, if_pos ht]
  rw [dt_apply, hev.deriv_eq, hval]
  exact hinner.exp.deriv

/-- **Base case.** The heat kernel is a positive classical solution of the linear heat equation
`∂_t Z = ∂_x² Z` on `t > 0`, i.e. of the multiplicative stochastic heat equation with zero
noise. -/
theorem heatKernel_solves_heat {t : ℝ} (ht : 0 < t) (x : ℝ) :
    dt heatKernel t x = dx (dx heatKernel) t x := by
  rw [dt_heatKernel ht, dx_dx_heatKernel ht]

/-! ## Main statement -/

/-- **Hairer's KPZ equation, Cole–Hopf reduction and base case.**

The KPZ equation `∂_t h = ∂_x² h + (∂_x h)² + ξ` is, at the level of classical solutions,
equivalent via the Cole–Hopf transform `h = log Z`, `Z = exp h` to the *linear* multiplicative
stochastic heat equation `∂_t Z = ∂_x² Z + Z ξ`: the transform is a regularity-preserving
bijection between positive solutions of the latter and solutions of the former.  This is the
deterministic backbone of Hairer's solution theory for KPZ.  In addition the equation is
solvable in the base case of a spatially homogeneous continuous noise, and the Gaussian heat
kernel is a positive classical solution of the linear equation `∂_t Z = ∂_x² Z` for `t > 0`. -/
theorem hairer_KPZ :
    (∀ xi Z : ℝ → ℝ → ℝ, SpaceTimeReg Z → (∀ t x : ℝ, 0 < Z t x) → IsSHESolution xi Z →
        SpaceTimeReg (fun t x => Real.log (Z t x)) ∧
          IsKPZSolution xi (fun t x => Real.log (Z t x))) ∧
    (∀ xi h : ℝ → ℝ → ℝ, SpaceTimeReg h → IsKPZSolution xi h →
        SpaceTimeReg (fun t x => Real.exp (h t x)) ∧ (∀ t x : ℝ, 0 < Real.exp (h t x)) ∧
          IsSHESolution xi (fun t x => Real.exp (h t x))) ∧
    (∀ Z : ℝ → ℝ → ℝ, (∀ t x : ℝ, 0 < Z t x) →
        (fun t x => Real.exp (Real.log (Z t x))) = Z) ∧
    (∀ h : ℝ → ℝ → ℝ, (fun t x => Real.log (Real.exp (h t x))) = h) ∧
    (∀ g : ℝ → ℝ, Continuous g → ∀ a : ℝ,
        ∃ h : ℝ → ℝ → ℝ, SpaceTimeReg h ∧ IsKPZSolution (fun t _ => g t) h ∧
          ∀ x : ℝ, h 0 x = a * x) ∧
    (∀ t x : ℝ, 0 < t →
        heatKernel t x = Real.exp (-(x ^ 2) / (4 * t)) / Real.sqrt (4 * Real.pi * t) ∧
          0 < heatKernel t x ∧ dt heatKernel t x = dx (dx heatKernel) t x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro xi Z hreg hpos hZ
    exact ⟨SpaceTimeReg.log Z hreg hpos, isKPZSolution_log xi Z hreg hpos hZ⟩
  · intro xi h hreg hh
    exact ⟨SpaceTimeReg.exp h hreg, fun t x => Real.exp_pos _, isSHESolution_exp xi h hreg hh⟩
  · intro Z hpos
    funext t x
    exact Real.exp_log (hpos t x)
  · intro h
    funext t x
    exact Real.log_exp (h t x)
  · intro g hg a
    obtain ⟨hreg, hsol⟩ := isKPZSolution_explicit g hg a
    exact ⟨_, hreg, hsol, fun x => by simp⟩
  · intro t x ht
    exact ⟨heatKernel_eq ht x, heatKernel_pos ht x, heatKernel_solves_heat ht x⟩

end Frontier

#print axioms Frontier.hairer_KPZ

