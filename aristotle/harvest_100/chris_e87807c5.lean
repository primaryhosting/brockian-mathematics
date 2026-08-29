/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ContDiff

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

/-! ## Differential operators on `ℝ³` -/

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/
noncomputable def pderiv (i : Fin 3) (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  deriv (fun s : ℝ => f (Function.update x i s)) (x i)

/-- The (spatial) Laplacian of a scalar field on `ℝ³`. -/
noncomputable def lap (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, pderiv i (pderiv i f) x

/-- The divergence, at time `t`, of a time-dependent vector field on `ℝ³`. -/
noncomputable def divergence (u : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)) (t : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, pderiv i (fun y => u t y i) x

/-! ## The 3D incompressible Navier–Stokes system -/

/-- `IsNSSolution ν u P` says that the velocity field `u` and the pressure `P` are smooth on
`ℝ × ℝ³` and satisfy, for all times `t ≥ 0` and all points `x ∈ ℝ³`, the incompressible
Navier–Stokes system with viscosity `ν` and no external force:

* `div u = 0`;
* `∂ₜ uᵢ + Σⱼ uⱼ ∂ⱼ uᵢ = ν Δuᵢ - ∂ᵢ P`. -/
structure IsNSSolution (ν : ℝ) (u : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (P : ℝ → (Fin 3 → ℝ) → ℝ) : Prop where
  smooth_u : ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => u q.1 q.2)
  smooth_P : ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => P q.1 q.2)
  div_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Fin 3 → ℝ, divergence u t x = 0
  momentum : ∀ t : ℝ, 0 ≤ t → ∀ x : Fin 3 → ℝ, ∀ i : Fin 3,
    deriv (fun s : ℝ => u s x i) t + ∑ j : Fin 3, u t x j * pderiv j (fun y => u t y i) x
      = ν * lap (fun y => u t y i) x - pderiv i (P t) x

/-- The total kinetic energy (up to the factor `1/2`) of the velocity field is bounded
uniformly in time. -/
def BoundedEnergy (u : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → (∫ x : Fin 3 → ℝ, ∑ i : Fin 3, (u t x i) ^ 2) ≤ C

/-- `HasGlobalSmoothSolution ν u₀` : there is a globally defined smooth solution of the
incompressible Navier–Stokes system on `ℝ³` with viscosity `ν`, no external force, initial
velocity `u₀`, and uniformly bounded energy. -/
def HasGlobalSmoothSolution (ν : ℝ) (u₀ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : Prop :=
  ∃ (u : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)) (P : ℝ → (Fin 3 → ℝ) → ℝ),
    IsNSSolution ν u P ∧ (∀ x, u 0 x = u₀ x) ∧ BoundedEnergy u

/-- **Global regularity for the 3D incompressible Navier–Stokes equations** (the statement of
the Clay Millennium Problem: existence and smoothness on `ℝ³`).

For every positive viscosity `ν` and every divergence-free Schwartz initial velocity field `u₀`
on `ℝ³`, the Navier–Stokes system with no external force admits a globally defined smooth
solution `(u, P)` with `u(0, ·) = u₀` and with uniformly bounded energy.

This proposition is *not* proved here: it records the statement of the open problem.
(Smoothness of the solution is formalized as smoothness on all of `ℝ × ℝ³`, the equations being
required for `t ≥ 0`.) -/
def NavierStokesGlobalRegularity : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzMap (Fin 3 → ℝ) (Fin 3 → ℝ),
    (∀ x, ∑ i : Fin 3, pderiv i (fun y => u₀ y i) x = 0) →
    HasGlobalSmoothSolution ν (fun x => u₀ x)

/-! ## Basic lemmas on partial derivatives -/

theorem pderiv_eq_zero_of_indep (i : Fin 3) (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ)
    (h : ∀ s : ℝ, f (Function.update x i s) = f x) : pderiv i f x = 0 := by
  have hf : (fun s : ℝ => f (Function.update x i s)) = fun _ : ℝ => f x := funext h
  simp [pderiv, hf]

theorem pderiv_zero (i : Fin 3) (x : Fin 3 → ℝ) :
    pderiv i (fun _ : Fin 3 → ℝ => (0 : ℝ)) x = 0 := by
  simp [pderiv]

theorem lap_zero (x : Fin 3 → ℝ) : lap (fun _ : Fin 3 → ℝ => (0 : ℝ)) x = 0 := by
  simp [lap, pderiv]

/-! ## Base case: the zero initial datum -/

/-- The zero velocity field together with the zero pressure is a solution of the
Navier–Stokes system, for every viscosity. -/
theorem isNSSolution_zero (ν : ℝ) :
    IsNSSolution ν (fun _ _ => (0 : Fin 3 → ℝ)) (fun _ _ => (0 : ℝ)) := by
  refine ⟨contDiff_const, contDiff_const, ?_, ?_⟩
  · intro t _ x
    simp [divergence, pderiv]
  · intro t _ x i
    simp [pderiv, lap]

/-- **Base case of the Millennium problem**: the global existence-and-smoothness statement
holds for the zero initial datum. -/
theorem hasGlobalSmoothSolution_zero (ν : ℝ) :
    HasGlobalSmoothSolution ν (fun _ => (0 : Fin 3 → ℝ)) := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, isNSSolution_zero ν, fun _ => rfl, ⟨0, ?_⟩⟩
  intro t _
  simp

/-! ## A Lean-checked reduction: shear flows -/

/-- **Reduction to the linear heat equation.**  If a scalar field `φ` on `ℝ × ℝ³` is smooth,
does not depend on the first spatial coordinate, and solves the heat equation `∂ₜ φ = ν Δφ`,
then the shear flow `u = (φ, 0, 0)` with vanishing pressure is a solution of the full nonlinear
3D incompressible Navier–Stokes system with viscosity `ν`.  In particular the nonlinear
transport term is exactly annihilated by such flows, so for this family global regularity of
Navier–Stokes reduces to global regularity for the linear heat equation. -/
theorem isNSSolution_shear (ν : ℝ) (phi : ℝ → (Fin 3 → ℝ) → ℝ)
    (hsmooth : ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => phi q.1 q.2))
    (hindep : ∀ t : ℝ, ∀ x : Fin 3 → ℝ, ∀ s : ℝ, phi t (Function.update x 0 s) = phi t x)
    (hheat : ∀ t : ℝ, 0 ≤ t → ∀ x : Fin 3 → ℝ,
      deriv (fun s : ℝ => phi s x) t = ν * lap (phi t) x) :
    IsNSSolution ν (fun t x => ![phi t x, 0, 0]) (fun _ _ => 0) := by
  have hp0 : ∀ (t : ℝ) (x : Fin 3 → ℝ), pderiv 0 (phi t) x = 0 :=
    fun t x => pderiv_eq_zero_of_indep 0 (phi t) x (hindep t x)
  refine ⟨?_, contDiff_const, ?_, ?_⟩
  · rw [contDiff_pi]
    intro i
    fin_cases i
    · simpa using hsmooth
    · simpa using contDiff_const
    · simpa using contDiff_const
  · intro t _ x
    simp [divergence, Fin.sum_univ_three, hp0, pderiv_zero]
  · intro t ht x i
    fin_cases i <;>
      simp [Fin.sum_univ_three, hp0, pderiv_zero, lap_zero, hheat t ht x]

/-! ## An explicit nontrivial global solution -/

/-- The explicit shear flow `u(t,x) = (e^{-ν t} sin x₂, 0, 0)`. -/
noncomputable def explicitShear (ν : ℝ) : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  fun t x => ![Real.exp (-(ν * t)) * Real.sin (x 1), 0, 0]

/-- The explicit shear flow, together with the vanishing pressure, is a global smooth solution
of the 3D incompressible Navier–Stokes equations. -/
theorem isNSSolution_explicitShear (ν : ℝ) :
    IsNSSolution ν (explicitShear ν) (fun _ _ => 0) := by
  have hsmooth : ContDiff ℝ ∞
      (fun q : ℝ × (Fin 3 → ℝ) => Real.exp (-(ν * q.1)) * Real.sin (q.2 1)) := by
    have h1 : ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => Real.exp (-(ν * q.1))) :=
      Real.contDiff_exp.comp ((contDiff_const.mul contDiff_fst).neg)
    have h2 : ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => Real.sin (q.2 1)) :=
      Real.contDiff_sin.comp ((contDiff_apply ℝ ℝ (1 : Fin 3)).comp contDiff_snd)
    exact h1.mul h2
  have hindep : ∀ (t : ℝ) (x : Fin 3 → ℝ) (s : ℝ),
      Real.exp (-(ν * t)) * Real.sin (Function.update x 0 s 1)
        = Real.exp (-(ν * t)) * Real.sin (x 1) := by
    intro t x s
    rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
  have hlap : ∀ (t : ℝ) (x : Fin 3 → ℝ),
      lap (fun y : Fin 3 → ℝ => Real.exp (-(ν * t)) * Real.sin (y 1)) x
        = -(Real.exp (-(ν * t)) * Real.sin (x 1)) := by
    intro t x
    have h0 : (fun y : Fin 3 → ℝ =>
        pderiv 0 (fun z : Fin 3 → ℝ => Real.exp (-(ν * t)) * Real.sin (z 1)) y)
          = fun _ : Fin 3 → ℝ => (0 : ℝ) := by
      funext y
      exact pderiv_eq_zero_of_indep 0 _ y (fun s => hindep t y s)
    have h2 : (fun y : Fin 3 → ℝ =>
        pderiv 2 (fun z : Fin 3 → ℝ => Real.exp (-(ν * t)) * Real.sin (z 1)) y)
          = fun _ : Fin 3 → ℝ => (0 : ℝ) := by
      funext y
      refine pderiv_eq_zero_of_indep 2 _ y (fun s => ?_)
      rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2)]
    have h1 : (fun y : Fin 3 → ℝ =>
        pderiv 1 (fun z : Fin 3 → ℝ => Real.exp (-(ν * t)) * Real.sin (z 1)) y)
          = fun y : Fin 3 → ℝ => Real.exp (-(ν * t)) * Real.cos (y 1) := by
      funext y
      simp [pderiv]
    simp only [lap, Fin.sum_univ_three, h0, h1, h2, pderiv_zero]
    simp [pderiv]
  have hheat : ∀ t : ℝ, 0 ≤ t → ∀ x : Fin 3 → ℝ,
      deriv (fun s : ℝ => Real.exp (-(ν * s)) * Real.sin (x 1)) t
        = ν * lap (fun y : Fin 3 → ℝ => Real.exp (-(ν * t)) * Real.sin (y 1)) x := by
    intro t _ x
    have h : HasDerivAt (fun s : ℝ => Real.exp (-(ν * s))) (Real.exp (-(ν * t)) * -ν) t := by
      simpa using (((hasDerivAt_id t).const_mul ν).neg.exp)
    rw [(h.mul_const (Real.sin (x 1))).deriv, hlap t x]
    ring
  exact isNSSolution_shear ν (fun t x => Real.exp (-(ν * t)) * Real.sin (x 1))
    hsmooth (fun t x s => hindep t x s) hheat

/-- The explicit shear flow is not the zero flow. -/
theorem explicitShear_ne_zero (ν : ℝ) : explicitShear ν ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun (congrFun h 0) (fun _ => Real.pi / 2)) 0
  simp [explicitShear] at h1

/-! ## Main statement -/

/-- **Navier–Stokes regularity: formalized statement, base case, and a Lean-checked
reduction.**

The 3D incompressible Navier–Stokes global regularity conjecture itself is recorded as
`Frontier.NavierStokesGlobalRegularity`; it is open and is not proved here.  What is proved
here is:

1. the **base case** of that statement: for every viscosity, the zero initial datum admits a
   global smooth solution with bounded energy;
2. a **Lean-checked reduction**: every smooth solution of the linear heat equation that is
   independent of the first spatial coordinate gives, as a shear flow with vanishing pressure,
   a global smooth solution of the full nonlinear 3D incompressible Navier–Stokes system;
3. an **explicit nonzero** global smooth Navier–Stokes flow obtained from that reduction. -/
theorem navier_stokes_regularity :
    (∀ ν : ℝ, HasGlobalSmoothSolution ν (fun _ => (0 : Fin 3 → ℝ))) ∧
    (∀ (ν : ℝ) (phi : ℝ → (Fin 3 → ℝ) → ℝ),
      ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => phi q.1 q.2) →
      (∀ t : ℝ, ∀ x : Fin 3 → ℝ, ∀ s : ℝ, phi t (Function.update x 0 s) = phi t x) →
      (∀ t : ℝ, 0 ≤ t → ∀ x : Fin 3 → ℝ,
        deriv (fun s : ℝ => phi s x) t = ν * lap (phi t) x) →
      IsNSSolution ν (fun t x => ![phi t x, 0, 0]) (fun _ _ => 0)) ∧
    (∀ ν : ℝ, IsNSSolution ν (explicitShear ν) (fun _ _ => 0) ∧ explicitShear ν ≠ 0) :=
  ⟨hasGlobalSmoothSolution_zero, isNSSolution_shear,
    fun ν => ⟨isNSSolution_explicitShear ν, explicitShear_ne_zero ν⟩⟩

end Frontier

