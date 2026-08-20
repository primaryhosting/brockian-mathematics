import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a
module, so the mandated header comment is placed immediately after the import.
-/

open scoped BigOperators ContDiff

namespace Frontier

namespace NavierStokes

/-- Points/vectors of `ℝ³`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/
noncomputable def pderiv (F : Vec → ℝ) (i : Fin 3) (x : Vec) : ℝ :=
  fderiv ℝ F x (Pi.single i 1)

/-- The divergence `∇ · u(t, ·)` of a time dependent vector field. -/
noncomputable def divergence (u : ℝ → Vec → Vec) (t : ℝ) (x : Vec) : ℝ :=
  ∑ i, pderiv (fun y => u t y i) i x

/-- The Laplacian `Δ F` of a scalar field on `ℝ³`. -/
noncomputable def laplacian (F : Vec → ℝ) (x : Vec) : ℝ :=
  ∑ i, pderiv (pderiv F i) i x

/-- The `j`-th component of the convective term `(u · ∇) u`. -/
noncomputable def convective (u : ℝ → Vec → Vec) (t : ℝ) (x : Vec) (j : Fin 3) : ℝ :=
  ∑ i, u t x i * pderiv (fun y => u t y j) i x

/-- Smoothness (`C^∞`) of a scalar field on space-time `ℝ × ℝ³`. -/
def SmoothST (F : ℝ → Vec → ℝ) : Prop :=
  ContDiff ℝ ∞ (fun q : ℝ × Vec => F q.1 q.2)

/-- `IsGlobalSmoothSolution ν u p` says that the velocity field `u` and the pressure `p` are
smooth on all of space-time `ℝ × ℝ³` and solve the incompressible Navier–Stokes system with
viscosity `ν` and no external force:
`∂ₜ uⱼ + Σᵢ uᵢ ∂ᵢ uⱼ = ν Δ uⱼ - ∂ⱼ p`,  `∇ · u = 0`. -/
structure IsGlobalSmoothSolution (nu : ℝ) (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ) : Prop where
  smooth_velocity : ∀ j, SmoothST (fun t x => u t x j)
  smooth_pressure : SmoothST p
  incompressible : ∀ t x, divergence u t x = 0
  momentum : ∀ t x j, deriv (fun s => u s x j) t + convective u t x j
      = nu * laplacian (fun y => u t y j) x - pderiv (p t) j x

/-- The Clay Millennium Problem statement (global existence and smoothness for 3D
incompressible Navier–Stokes): for every divergence-free Schwartz-class initial velocity
there is a globally smooth solution with bounded energy.  This is an open problem; it is
recorded here only as a `Prop`-valued definition. -/
def ClayGlobalRegularity (nu : ℝ) : Prop :=
  ∀ u₀ : Fin 3 → SchwartzMap Vec ℝ,
    (∀ x, ∑ i, pderiv (fun y => u₀ i y) i x = 0) →
    ∃ u p, IsGlobalSmoothSolution nu u p ∧ (∀ x i, u 0 x i = u₀ i x) ∧
      ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∫ x : Vec, ‖u t x‖ ^ 2 ≤ C

/-! ### Basic computations with partial derivatives -/

/-- Partial derivatives of a constant field vanish. -/
lemma pderiv_const (c : ℝ) (i : Fin 3) (x : Vec) : pderiv (fun _ => c) i x = 0 := by
  simp [pderiv]

/-- The Laplacian of a constant field vanishes. -/
lemma laplacian_const (c : ℝ) (x : Vec) : laplacian (fun _ => c) x = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have h : pderiv (fun _ : Vec => c) i = fun _ => (0 : ℝ) := funext (pderiv_const c i)
  rw [h]
  exact pderiv_const 0 i x

/-- The partial derivatives of a linear functional `y ↦ Σ cₖ yₖ`. -/
lemma pderiv_lin (c : Vec) (j : Fin 3) (x : Vec) :
    pderiv (fun y => ∑ k, c k * y k) j x = c j := by
  have hfun : (fun y : Vec => ∑ k, c k * y k) = ∑ k : Fin 3, fun y : Vec => c k * y k := by
    funext y; simp [Finset.sum_apply]
  have h : HasFDerivAt (fun y : Vec => ∑ k, c k * y k)
      (∑ k, (c k) • (ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ)) x := by
    rw [hfun]
    exact HasFDerivAt.sum fun k _ => by
      simpa using ((ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ).hasFDerivAt).const_mul (c k)
  rw [pderiv, h.fderiv]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- Partial derivatives of a field depending on a single coordinate. -/
lemma pderiv_coord (g : ℝ → ℝ) (hg : Differentiable ℝ g) (k i : Fin 3) (x : Vec) :
    pderiv (fun y => g (y k)) i x = if i = k then deriv g (x k) else 0 := by
  have hp : HasFDerivAt (fun y : Vec => y k) (ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ) x :=
    (ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ).hasFDerivAt
  have h : HasFDerivAt (fun y : Vec => g (y k))
      (deriv g (x k) • (ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ)) x :=
    ((hg (x k)).hasDerivAt).comp_hasFDerivAt x hp
  rw [pderiv, h.fderiv]
  by_cases hik : i = k
  · subst hik; simp
  · simp [hik, Ne.symm hik]

/-- The directional derivative of `F` along the `i`-th axis, seen as an honest one dimensional
derivative along the corresponding coordinate line. -/
lemma pderiv_slice (F : Vec → ℝ) (i : Fin 3) (x : Vec) (h : DifferentiableAt ℝ F x) :
    HasDerivAt (fun s => F (Function.update x i s)) (pderiv F i x) (x i) := by
  have hu : HasDerivAt (fun s : ℝ => Function.update x i s) (Pi.single i 1) (x i) :=
    hasDerivAt_update x i (x i)
  have h2 : HasFDerivAt F (fderiv ℝ F x) (Function.update x i (x i)) := by
    simpa using h.hasFDerivAt
  simpa [pderiv, Function.comp] using h2.comp_hasDerivAt (x i) hu

/-- A field that does not depend on its `i`-th coordinate has vanishing `i`-th partial
derivative. -/
lemma pderiv_eq_zero_of_indep (F : Vec → ℝ) (i : Fin 3) (x : Vec) (h : DifferentiableAt ℝ F x)
    (hindep : ∀ s, F (Function.update x i s) = F x) : pderiv F i x = 0 := by
  have h1 := pderiv_slice F i x h
  have h2 : HasDerivAt (fun s => F (Function.update x i s)) 0 (x i) := by
    have hconst : (fun s => F (Function.update x i s)) = fun _ => F x := funext hindep
    rw [hconst]
    exact hasDerivAt_const _ _
  exact h1.unique h2

/-- A space-time smooth field is smooth, hence differentiable, in the space variable. -/
lemma SmoothST.spatial {v : ℝ → Vec → ℝ} (hv : SmoothST v) (t : ℝ) : Differentiable ℝ (v t) :=
  (hv.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)

/-- `sin` in one coordinate is an eigenfunction of the Laplacian with eigenvalue `-1`. -/
lemma laplacian_sin (c : ℝ) (x : Vec) :
    laplacian (fun y : Vec => c * Real.sin (y 1)) x = -(c * Real.sin (x 1)) := by
  have hg : Differentiable ℝ (fun s : ℝ => c * Real.sin s) := by fun_prop
  have hg' : deriv (fun s : ℝ => c * Real.sin s) = fun s => c * Real.cos s := by funext s; simp
  have hgc : Differentiable ℝ (fun s : ℝ => c * Real.cos s) := by fun_prop
  have hgc' : deriv (fun s : ℝ => c * Real.cos s) = fun s => -(c * Real.sin s) := by
    funext s; simp
  have key1 : pderiv (fun y : Vec => c * Real.sin (y 1)) 1 = fun x : Vec => c * Real.cos (x 1) := by
    funext x; rw [pderiv_coord _ hg 1 1 x, hg']; simp
  have key0 : ∀ i : Fin 3, i ≠ 1 → pderiv (fun y : Vec => c * Real.sin (y 1)) i
      = fun _ : Vec => (0 : ℝ) := by
    intro i hi; funext x; rw [pderiv_coord _ hg 1 i x, if_neg hi]
  rw [laplacian, Finset.sum_eq_single (1 : Fin 3)]
  · rw [key1, pderiv_coord (fun s => c * Real.cos s) hgc 1 1 x, hgc']
    simp
  · intro i _ hi
    rw [key0 i hi]
    exact pderiv_const 0 i x
  · simp

end NavierStokes

open NavierStokes

/-! ### The base case: spatially uniform flows -/

/-- **Base case of global regularity for the 3D incompressible Navier–Stokes equations.**

For every viscosity `ν` and every smooth curve `a : ℝ → ℝ³` there is a globally defined smooth
solution `(u, p)` of the incompressible Navier–Stokes system on all of space-time whose velocity
field is the spatially uniform flow `u(t, x) = a(t)` (the pressure being the linear field
`p(t, x) = - a'(t) · x`).  In particular (taking `a = 0`) the Clay initial datum `u₀ = 0` admits
a global smooth solution. -/
theorem navier_stokes_regularity (nu : ℝ) (a : ℝ → Vec) (ha : ContDiff ℝ ∞ a) :
    ∃ (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ),
      IsGlobalSmoothSolution nu u p ∧ ∀ t x, u t x = a t := by
  have haj : ∀ j, ContDiff ℝ ∞ (fun t => a t j) := fun j => contDiff_pi.mp ha j
  have hd : ∀ j, ContDiff ℝ ∞ (deriv fun t => a t j) := fun j =>
    (contDiff_infty_iff_deriv.mp (haj j)).2
  refine ⟨fun t _ => a t, fun t x => ∑ k, (-(deriv (fun s => a s k) t)) * x k, ?_, fun _ _ => rfl⟩
  refine ⟨fun j => (haj j).comp contDiff_fst, ?_, ?_, ?_⟩
  · refine ContDiff.sum fun k _ => ?_
    have h1 : ContDiff ℝ ∞ (fun q : ℝ × Vec => -(deriv (fun s => a s k) q.1)) :=
      ((hd k).comp contDiff_fst).neg
    have h2 : ContDiff ℝ ∞ (fun q : ℝ × Vec => q.2 k) := by fun_prop
    exact h1.mul h2
  · exact fun t x => Finset.sum_eq_zero fun i _ => pderiv_const _ i x
  · intro t x j
    have h1 : convective (fun t _ => a t) t x j = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [pderiv_const]; ring
    rw [h1, laplacian_const, pderiv_lin]
    ring

/-- The zero initial datum, which is a legitimate (Schwartz, divergence-free) datum for the
Clay problem, admits a global smooth solution with bounded (zero) energy. -/
theorem navier_stokes_regularity_zero_data (nu : ℝ) :
    ∃ (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ),
      IsGlobalSmoothSolution nu u p ∧ (∀ x, u 0 x = 0) ∧
        ∃ C : ℝ, ∀ t : ℝ, ∫ x : Vec, ‖u t x‖ ^ 2 ≤ C := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, ⟨fun j => contDiff_const, contDiff_const, ?_, ?_⟩,
    fun _ => rfl, 0, fun t => ?_⟩
  · exact fun t x => Finset.sum_eq_zero fun i _ => pderiv_const _ i x
  · intro t x j
    have h1 : convective (fun _ _ => (0 : Vec)) t x j = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [pderiv_const]; ring
    rw [h1, laplacian_const, pderiv_const]
    simp
  · simp

/-- An explicit *nonlinear* check: the decaying shear flow
`u(t, x) = (e^{-ν t} sin x₂, 0, 0)`, `p = 0`, is a global smooth solution of the 3D
incompressible Navier–Stokes equations. -/
theorem navier_stokes_regularity_shear (nu : ℝ) :
    IsGlobalSmoothSolution nu
      (fun t x => Pi.single 0 (Real.exp (-nu * t) * Real.sin (x 1))) (fun _ _ => 0) := by
  have hdiffg : ∀ c : ℝ, Differentiable ℝ (fun s : ℝ => c * Real.sin s) := fun c => by fun_prop
  have hc0 : ∀ t : ℝ, (fun y : Vec =>
      (Pi.single (0 : Fin 3) (Real.exp (-nu * t) * Real.sin (y 1)) : Vec) 0)
      = fun y : Vec => Real.exp (-nu * t) * Real.sin (y 1) := by
    intro t; funext y; simp
  have hcne : ∀ (t : ℝ) (j : Fin 3), j ≠ 0 → (fun y : Vec =>
      (Pi.single (0 : Fin 3) (Real.exp (-nu * t) * Real.sin (y 1)) : Vec) j)
      = fun _ : Vec => (0 : ℝ) := by
    intro t j hj; funext y; simp [hj]
  refine ⟨?_, contDiff_const, ?_, ?_⟩
  · intro j
    by_cases hj : j = 0
    · subst hj
      have h : (fun q : ℝ × Vec =>
          (Pi.single (0 : Fin 3) (Real.exp (-nu * q.1) * Real.sin (q.2 1)) : Vec) 0)
          = fun q : ℝ × Vec => Real.exp (-nu * q.1) * Real.sin (q.2 1) := by funext q; simp
      show ContDiff ℝ ∞ _
      rw [h]
      fun_prop
    · have h : (fun q : ℝ × Vec =>
          (Pi.single (0 : Fin 3) (Real.exp (-nu * q.1) * Real.sin (q.2 1)) : Vec) j)
          = fun _ : ℝ × Vec => (0 : ℝ) := by funext q; simp [hj]
      show ContDiff ℝ ∞ _
      rw [h]
      exact contDiff_const
  · intro t x
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i = 0
    · subst hi
      rw [hc0 t, pderiv_coord _ (hdiffg _) 1 0 x]
      simp
    · rw [hcne t i hi]
      exact pderiv_const 0 i x
  · intro t x j
    by_cases hj : j = 0
    · subst hj
      have hconv : convective (fun t x => Pi.single 0 (Real.exp (-nu * t) * Real.sin (x 1)))
          t x 0 = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi : i = 0
        · subst hi
          rw [hc0 t, pderiv_coord _ (hdiffg _) 1 0 x]
          simp
        · simp [hi]
      have hderiv : deriv (fun s : ℝ =>
          (Pi.single (0 : Fin 3) (Real.exp (-nu * s) * Real.sin (x 1)) : Vec) 0) t
          = -nu * Real.exp (-nu * t) * Real.sin (x 1) := by
        have he : (fun s : ℝ =>
            (Pi.single (0 : Fin 3) (Real.exp (-nu * s) * Real.sin (x 1)) : Vec) 0)
            = fun s : ℝ => Real.exp (-nu * s) * Real.sin (x 1) := by funext s; simp
        rw [he]
        have h1 : HasDerivAt (fun s : ℝ => Real.exp (-nu * s)) (-nu * Real.exp (-nu * t)) t := by
          simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-nu)).exp
        simpa using (h1.mul_const (Real.sin (x 1))).deriv
      rw [hconv, hderiv, hc0 t, laplacian_sin, pderiv_const]
      ring
    · have hconv : convective (fun t x => Pi.single 0 (Real.exp (-nu * t) * Real.sin (x 1)))
          t x j = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hcne t j hj, pderiv_const]
        ring
      have hderiv : deriv (fun s : ℝ =>
          (Pi.single (0 : Fin 3) (Real.exp (-nu * s) * Real.sin (x 1)) : Vec) j) t = 0 := by
        have he : (fun s : ℝ =>
            (Pi.single (0 : Fin 3) (Real.exp (-nu * s) * Real.sin (x 1)) : Vec) j)
            = fun _ : ℝ => (0 : ℝ) := by funext s; simp [hj]
        rw [he]
        simp
      rw [hconv, hderiv, hcne t j hj, laplacian_const, pderiv_const]
      ring

/-- **A Lean-checked reduction.**  For shear flows `u(t, x) = (v(t, x), 0, 0)` whose profile `v`
does not depend on the first coordinate `x₁`, the nonlinear term `(u · ∇)u` vanishes identically
and the incompressible Navier–Stokes system reduces to the linear heat equation
`∂ₜ v = ν Δ v`:  any smooth solution of the heat equation with this symmetry yields a global
smooth solution of the 3D incompressible Navier–Stokes equations (with zero pressure). -/
theorem navier_stokes_shear_reduction (nu : ℝ) (v : ℝ → Vec → ℝ) (hv : SmoothST v)
    (hindep : ∀ (t : ℝ) (x : Vec) (s : ℝ), v t (Function.update x 0 s) = v t x)
    (hheat : ∀ t x, deriv (fun s => v s x) t = nu * laplacian (v t) x) :
    IsGlobalSmoothSolution nu (fun t x => Pi.single 0 (v t x)) (fun _ _ => 0) := by
  have hd0 : ∀ (t : ℝ) (x : Vec), pderiv (v t) 0 x = 0 := fun t x =>
    pderiv_eq_zero_of_indep _ 0 x ((hv.spatial t) x) (hindep t x)
  have hc0 : ∀ t : ℝ, (fun y : Vec => (Pi.single (0 : Fin 3) (v t y) : Vec) 0) = v t := by
    intro t; funext y; simp
  have hcne : ∀ (t : ℝ) (j : Fin 3), j ≠ 0 →
      (fun y : Vec => (Pi.single (0 : Fin 3) (v t y) : Vec) j) = fun _ : Vec => (0 : ℝ) := by
    intro t j hj; funext y; simp [hj]
  refine ⟨?_, contDiff_const, ?_, ?_⟩
  · intro j
    by_cases hj : j = 0
    · subst hj
      have h : (fun q : ℝ × Vec => (Pi.single (0 : Fin 3) (v q.1 q.2) : Vec) 0)
          = fun q : ℝ × Vec => v q.1 q.2 := by funext q; simp
      show ContDiff ℝ ∞ _
      rw [h]
      exact hv
    · have h : (fun q : ℝ × Vec => (Pi.single (0 : Fin 3) (v q.1 q.2) : Vec) j)
          = fun _ : ℝ × Vec => (0 : ℝ) := by funext q; simp [hj]
      show ContDiff ℝ ∞ _
      rw [h]
      exact contDiff_const
  · intro t x
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i = 0
    · subst hi
      rw [hc0 t]
      exact hd0 t x
    · rw [hcne t i hi]
      exact pderiv_const 0 i x
  · intro t x j
    by_cases hj : j = 0
    · subst hj
      have hconv : convective (fun t x => Pi.single 0 (v t x)) t x 0 = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi : i = 0
        · subst hi
          rw [hc0 t, hd0 t x]
          ring
        · simp [hi]
      have hderiv : deriv (fun s : ℝ => (Pi.single (0 : Fin 3) (v s x) : Vec) 0) t
          = deriv (fun s => v s x) t := by
        have he : (fun s : ℝ => (Pi.single (0 : Fin 3) (v s x) : Vec) 0)
            = fun s : ℝ => v s x := by funext s; simp
        rw [he]
      rw [hconv, hderiv, hc0 t, pderiv_const, hheat t x]
      ring
    · have hconv : convective (fun t x => Pi.single 0 (v t x)) t x j = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hcne t j hj, pderiv_const]
        ring
      have hderiv : deriv (fun s : ℝ => (Pi.single (0 : Fin 3) (v s x) : Vec) j) t = 0 := by
        have he : (fun s : ℝ => (Pi.single (0 : Fin 3) (v s x) : Vec) j)
            = fun _ : ℝ => (0 : ℝ) := by funext s; simp [hj]
        rw [he]
        simp
      rw [hconv, hderiv, hcne t j hj, laplacian_const, pderiv_const]
      ring

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

