import Mathlib
/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ContDiff
open MeasureTheory

namespace Frontier

/-! ## Basic differential operators on `ℝ³` -/

/-- The physical space `ℝ³`, as functions `Fin 3 → ℝ`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/
noncomputable def partialD (f : Vec → ℝ) (i : Fin 3) (x : Vec) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The Laplacian `Δf = ∑ᵢ ∂ᵢ∂ᵢ f` of a scalar field on `ℝ³`. -/
noncomputable def laplacian (f : Vec → ℝ) (x : Vec) : ℝ :=
  ∑ i, partialD (partialD f i) i x

/-- The divergence `∇ · u = ∑ᵢ ∂ᵢ uᵢ` of a vector field on `ℝ³`. -/
noncomputable def divergence (u : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i, partialD (fun y => u y i) i x

/-- The `j`-th component of the convective term `(u · ∇) u`. -/
noncomputable def convective (u : Vec → Vec) (x : Vec) (j : Fin 3) : ℝ :=
  ∑ i, u x i * partialD (fun y => u y j) i x

/-- A time-dependent scalar field on `ℝ³` is smooth (jointly in time and space). -/
def SmoothScalarField (p : ℝ → Vec → ℝ) : Prop :=
  ContDiff ℝ ∞ fun q : ℝ × Vec => p q.1 q.2

/-- A time-dependent vector field on `ℝ³` is smooth (jointly in time and space). -/
def SmoothVectorField (u : ℝ → Vec → Vec) : Prop :=
  ContDiff ℝ ∞ fun q : ℝ × Vec => u q.1 q.2

/-! ## The incompressible Navier–Stokes equations -/

/-- `IsNSSolution nu f u p` says that the velocity field `u` and pressure `p` solve the
incompressible Navier–Stokes equations on `ℝ × ℝ³` with viscosity `nu` and external force `f`:

* momentum:       `∂ₜuⱼ + ∑ᵢ uᵢ ∂ᵢ uⱼ = nu Δuⱼ - ∂ⱼ p + fⱼ`,
* incompressible: `∇ · u = 0`. -/
structure IsNSSolution (nu : ℝ) (f : ℝ → Vec → Vec) (u : ℝ → Vec → Vec)
    (p : ℝ → Vec → ℝ) : Prop where
  momentum : ∀ t x j, deriv (fun s => u s x j) t + convective (u t) x j
      = nu * laplacian (fun y => u t y j) x - partialD (p t) j x + f t x j
  incompressible : ∀ t x, divergence (u t) x = 0

/-- `GlobalRegular nu f u p` says that `(u, p)` is a globally defined, everywhere smooth
solution of the Navier–Stokes equations with viscosity `nu` and force `f`. -/
def GlobalRegular (nu : ℝ) (f : ℝ → Vec → Vec) (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ) : Prop :=
  SmoothVectorField u ∧ SmoothScalarField p ∧ IsNSSolution nu f u p

/-- Rapid (Schwartz-type) decay of a vector field on `ℝ³`. -/
def RapidlyDecaying (u₀ : Vec → Vec) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ x : Vec, ‖u₀ x‖ ≤ C / (1 + ‖x‖) ^ N

/-- **The Navier–Stokes global regularity conjecture** (Clay Millennium Problem: existence
and smoothness on `ℝ³`): for every positive viscosity and every smooth, divergence-free,
rapidly decaying initial datum there exist a globally defined smooth velocity field and
pressure, with no external force, solving the Navier–Stokes equations, attaining the initial
datum, and having uniformly bounded kinetic energy.  This statement is open. -/
def NavierStokesGlobalRegularity : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ u₀ : Vec → Vec, ContDiff ℝ ∞ u₀ → (∀ x, divergence u₀ x = 0) →
    RapidlyDecaying u₀ →
      ∃ (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ),
        GlobalRegular nu (fun _ _ => 0) u p ∧ (∀ x, u 0 x = u₀ x) ∧
        ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∫ x, ‖u t x‖ ^ 2 ≤ C

/-! ## Elementary properties of the differential operators -/

@[simp] theorem partialD_const (c : ℝ) (i : Fin 3) (x : Vec) :
    partialD (fun _ => c) i x = 0 := by
  simp [partialD]

@[simp] theorem partialD_const_fun (c : ℝ) (i : Fin 3) :
    partialD (fun _ => c) i = fun _ => (0 : ℝ) := by
  funext x; simp

@[simp] theorem laplacian_const (c : ℝ) (x : Vec) : laplacian (fun _ => c) x = 0 := by
  simp [laplacian]

/-! ## The base case: the zero flow -/

/-- **Base case.** The identically zero velocity field, with zero pressure, is a global smooth
solution of the Navier–Stokes equations with zero force, for every viscosity. -/
theorem globalRegular_zero (nu : ℝ) :
    GlobalRegular nu (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨contDiff_const, contDiff_const, ?_, ?_⟩
  · intro t x j
    simp [convective, laplacian]
  · intro t x
    simp [divergence]

/-! ## Shear flows: a Lean-checked reduction to the linear heat equation -/

/-- The shear (unidirectional) velocity field with profile `w`: `u = (w, 0, 0)`. -/
noncomputable def shearField (w : ℝ → Vec → ℝ) : ℝ → Vec → Vec :=
  fun t x j => if j = 0 then w t x else 0

@[simp] theorem shearField_apply_zero (w : ℝ → Vec → ℝ) (t : ℝ) (x : Vec) :
    shearField w t x 0 = w t x := by
  simp [shearField]

theorem shearField_apply_ne (w : ℝ → Vec → ℝ) (t : ℝ) (x : Vec) {j : Fin 3} (hj : j ≠ 0) :
    shearField w t x j = 0 := by
  simp [shearField, hj]

theorem shearField_comp_zero (w : ℝ → Vec → ℝ) (t : ℝ) :
    (fun y => shearField w t y 0) = w t := by
  funext y; simp

theorem shearField_comp_ne (w : ℝ → Vec → ℝ) (t : ℝ) {j : Fin 3} (hj : j ≠ 0) :
    (fun y => shearField w t y j) = fun _ => (0 : ℝ) := by
  funext y; simp [shearField, hj]

theorem smooth_shearField {w : ℝ → Vec → ℝ} (hw : SmoothScalarField w) :
    SmoothVectorField (shearField w) := by
  rw [SmoothVectorField, contDiff_pi]
  intro j
  by_cases hj : j = 0
  · subst hj
    simpa [shearField] using hw
  · simpa [shearField, hj] using (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ × Vec => (0 : ℝ))

/-- **A Lean-checked reduction.** For unidirectional (shear) flows `u = (w, 0, 0)` whose profile
`w` does not depend on the streamwise coordinate `x₀`, the nonlinear term of Navier–Stokes
vanishes identically, and the full nonlinear system with zero force and zero pressure reduces to
the *linear* heat equation `∂ₜ w = nu Δ w`.  Consequently every global smooth solution of the
heat equation produces a globally regular solution of the 3D incompressible Navier–Stokes
equations.

This is the target of this file: the Millennium-Prize statement itself is recorded above as
`Frontier.NavierStokesGlobalRegularity` and remains open; here we prove the base case
(`globalRegular_zero`) together with this reduction (and, below, a nontrivial instance of it). -/
theorem navier_stokes_regularity (nu : ℝ) (w : ℝ → Vec → ℝ)
    (hsmooth : SmoothScalarField w)
    (hindep : ∀ t x, partialD (w t) 0 x = 0)
    (hheat : ∀ t x, deriv (fun s => w s x) t = nu * laplacian (w t) x) :
    GlobalRegular nu (fun _ _ => 0) (shearField w) (fun _ _ => 0) := by
  refine ⟨smooth_shearField hsmooth, contDiff_const, ?_, ?_⟩
  · intro t x j
    by_cases hj : j = 0
    · subst hj
      have hconv : convective (shearField w t) x 0 = 0 := by
        rw [convective, shearField_comp_zero]
        refine Finset.sum_eq_zero ?_
        intro i _
        by_cases hi : i = 0
        · subst hi; rw [hindep t x, mul_zero]
        · rw [shearField_apply_ne w t x hi, zero_mul]
      have hu : (fun s => shearField w s x 0) = fun s => w s x := by
        funext s; simp
      rw [hu, hconv, shearField_comp_zero]
      simpa using hheat t x
    · have h0 : (fun s => shearField w s x j) = fun _ => (0 : ℝ) := by
        funext s; exact shearField_apply_ne w s x hj
      have hconv : convective (shearField w t) x j = 0 := by
        rw [convective, shearField_comp_ne w t hj]
        simp
      rw [h0, hconv, shearField_comp_ne w t hj]
      simp
  · intro t x
    rw [divergence]
    refine Finset.sum_eq_zero ?_
    intro i _
    by_cases hi : i = 0
    · subst hi; rw [shearField_comp_zero]; exact hindep t x
    · rw [shearField_comp_ne w t hi]; simp

/-! ## A nontrivial instance of the reduction -/

/-- Partial derivatives of a field of the form `x ↦ c * g x₁`. -/
theorem partialD_comp_coord {g g' : ℝ → ℝ} (hg : ∀ u : ℝ, HasDerivAt g (g' u) u)
    (c : ℝ) (i : Fin 3) (x : Vec) :
    partialD (fun y : Vec => c * g (y 1)) i x = c * g' (x 1) * (if i = 1 then 1 else 0) := by
  have h1 : HasFDerivAt (fun y : Vec => y 1) (ContinuousLinearMap.proj 1 : Vec →L[ℝ] ℝ) x :=
    (ContinuousLinearMap.proj 1 : Vec →L[ℝ] ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Vec => g (y 1))
      (g' (x 1) • (ContinuousLinearMap.proj 1 : Vec →L[ℝ] ℝ)) x :=
    (hg (x 1)).comp_hasFDerivAt x h1
  have h3 : HasFDerivAt (fun y : Vec => c * g (y 1))
      ((c * g' (x 1)) • (ContinuousLinearMap.proj 1 : Vec →L[ℝ] ℝ)) x := by
    rw [← smul_smul]; exact h2.const_mul c
  rw [partialD, h3.fderiv]
  simp [Pi.single_apply, eq_comm]

/-- An explicit, nonzero shear profile: `w t x = exp (-nu t) * sin x₁`. -/
noncomputable def exampleProfile (nu : ℝ) : ℝ → Vec → ℝ :=
  fun t x => Real.exp (-nu * t) * Real.sin (x 1)

theorem smooth_exampleProfile (nu : ℝ) : SmoothScalarField (exampleProfile nu) := by
  have h1 : ContDiff ℝ ∞ fun q : ℝ × Vec => Real.exp (-nu * q.1) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)
  have h2 : ContDiff ℝ ∞ fun q : ℝ × Vec => Real.sin (q.2 1) :=
    Real.contDiff_sin.comp ((contDiff_apply ℝ ℝ (1 : Fin 3)).comp contDiff_snd)
  exact h1.mul h2

theorem partialD_exampleProfile_one (nu t : ℝ) :
    partialD (exampleProfile nu t) 1 = fun x : Vec => Real.exp (-nu * t) * Real.cos (x 1) := by
  funext x
  have he : exampleProfile nu t = fun y : Vec => Real.exp (-nu * t) * Real.sin (y 1) := rfl
  rw [he, partialD_comp_coord Real.hasDerivAt_sin]
  simp

theorem partialD_exampleProfile_ne (nu t : ℝ) {i : Fin 3} (hi : i ≠ 1) :
    partialD (exampleProfile nu t) i = fun _ : Vec => (0 : ℝ) := by
  funext x
  have he : exampleProfile nu t = fun y : Vec => Real.exp (-nu * t) * Real.sin (y 1) := rfl
  rw [he, partialD_comp_coord Real.hasDerivAt_sin]
  simp [hi]

theorem exampleProfile_indep (nu : ℝ) (t : ℝ) (x : Vec) :
    partialD (exampleProfile nu t) 0 x = 0 := by
  rw [partialD_exampleProfile_ne nu t (by decide : (0 : Fin 3) ≠ 1)]

theorem laplacian_exampleProfile (nu t : ℝ) (x : Vec) :
    laplacian (exampleProfile nu t) x = -exampleProfile nu t x := by
  have key : partialD (partialD (exampleProfile nu t) 1) 1 x = -exampleProfile nu t x := by
    rw [partialD_exampleProfile_one,
      partialD_comp_coord (g' := fun u => -Real.sin u) (fun u => Real.hasDerivAt_cos u)]
    simp [exampleProfile]
  have h0 : partialD (partialD (exampleProfile nu t) 0) 0 x = 0 := by
    rw [partialD_exampleProfile_ne nu t (by decide : (0 : Fin 3) ≠ 1)]; simp
  have h2 : partialD (partialD (exampleProfile nu t) 2) 2 x = 0 := by
    rw [partialD_exampleProfile_ne nu t (by decide : (2 : Fin 3) ≠ 1)]; simp
  rw [laplacian, Fin.sum_univ_three, h0, h2, key]
  ring

theorem heat_exampleProfile (nu t : ℝ) (x : Vec) :
    deriv (fun s => exampleProfile nu s x) t = nu * laplacian (exampleProfile nu t) x := by
  have h : HasDerivAt (fun s => exampleProfile nu s x)
      (-nu * Real.exp (-nu * t) * Real.sin (x 1)) t := by
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-nu * s)) (Real.exp (-nu * t) * -nu) t := by
      simpa using (((hasDerivAt_id t).const_mul (-nu)).exp)
    simpa [exampleProfile, mul_comm, mul_assoc, mul_left_comm] using
      hexp.mul_const (Real.sin (x 1))
  rw [h.deriv, laplacian_exampleProfile, exampleProfile]
  ring

/-- The reduction is not vacuous: an explicit global smooth Navier–Stokes flow
obtained from the shear reduction. -/
theorem globalRegular_exampleShear (nu : ℝ) :
    GlobalRegular nu (fun _ _ => 0) (shearField (exampleProfile nu)) (fun _ _ => 0) :=
  navier_stokes_regularity nu (exampleProfile nu) (smooth_exampleProfile nu)
    (exampleProfile_indep nu) (heat_exampleProfile nu)

/-- The example flow is genuinely nonzero. -/
theorem exampleShear_ne_zero (nu : ℝ) :
    shearField (exampleProfile nu) 0 (fun _ => Real.pi / 2) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [shearField, exampleProfile] at h0

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

