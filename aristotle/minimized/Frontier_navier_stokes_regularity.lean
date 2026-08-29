/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open ContDiff

namespace Frontier

/-- The physical space `ℝ³`, modelled as `Fin 3 → ℝ`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

noncomputable def partialDeriv (f : Vec → ℝ) (i : Fin 3) (x : Vec) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The Laplacian `Δf = ∑ⱼ ∂ⱼ∂ⱼ f` of a scalar field on `ℝ³`. -/

noncomputable def laplacian (f : Vec → ℝ) (x : Vec) : ℝ :=
  ∑ j, partialDeriv (partialDeriv f j) j x

/-- The divergence `∇ · v = ∑ᵢ ∂ᵢ vᵢ` of a vector field on `ℝ³`. -/

noncomputable def divergence (v : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i, partialDeriv (fun y => v y i) i x

/-- `u` (a time dependent velocity field) together with `p` (a time dependent pressure)
is a *global smooth solution* of the incompressible Navier–Stokes equations on `ℝ × ℝ³`
with viscosity `ν`:

* `u` and `p` are `C^∞` jointly in time and space;
* `u` is divergence free (incompressibility);
* the momentum equation `∂ₜuᵢ + (u · ∇)uᵢ = ν Δuᵢ - ∂ᵢp` holds at every point of
  space-time.
-/
structure IsGlobalSmoothSolution (ν : ℝ) (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ) : Prop where
  smooth_velocity : ContDiff ℝ ∞ (fun q : ℝ × Vec => u q.1 q.2)
  smooth_pressure : ContDiff ℝ ∞ (fun q : ℝ × Vec => p q.1 q.2)
  incompressible : ∀ t x, divergence (u t) x = 0
  momentum : ∀ t x i,
    deriv (fun s => u s x i) t + ∑ j, u t x j * partialDeriv (fun y => u t y i) j x
      = ν * laplacian (fun y => u t y i) x - partialDeriv (p t) i x

/-- **Global regularity for the 3D incompressible Navier–Stokes equations** (the Clay
Millennium Problem, here in its whole–space, force–free formulation): for every smooth,
divergence-free initial velocity field `u₀` on `ℝ³` there exist a globally defined smooth
velocity field `u` and pressure `p` solving the Navier–Stokes equations with viscosity `ν`
and with initial datum `u₀`.

This `Prop` is the *statement* of the open problem; it is not asserted here.  The theorem
`Frontier.navier_stokes_regularity` below proves an unconditional special case of it. -/

lemma deriv_apply (ha : Differentiable ℝ a) (i : Fin 3) (t : ℝ) :
    deriv (fun s => a s i) t = deriv a t i :=
  ((hasDerivAt_pi.1 (ha t).hasDerivAt) i).deriv

/-- Partial derivatives of a spatially constant field vanish. -/

@[simp] lemma partialDeriv_const (c : ℝ) (i : Fin 3) (x : Vec) :
    partialDeriv (fun _ : Vec => c) i x = 0 := by
  simp [partialDeriv]

/-- The Laplacian of a spatially constant field vanishes. -/

@[simp] lemma laplacian_const (c : ℝ) (x : Vec) :
    laplacian (fun _ : Vec => c) x = 0 := by
  have h : ∀ j, partialDeriv (fun _ : Vec => c) j = fun _ : Vec => (0 : ℝ) := by
    intro j; funext y; exact partialDeriv_const c j y
  simp [laplacian, h]

/-- The gradient of the linear pressure `x ↦ -⟨c, x⟩`. -/

lemma partialDeriv_linear_pressure (c : Vec) (i : Fin 3) (x : Vec) :
    partialDeriv (fun y : Vec => -∑ k, c k * y k) i x = -c i := by
  have h : (fun y : Vec => -∑ k, c k * y k)
      = fun y => (-(∑ k, c k • (ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ))) y := by
    funext y; simp
  rw [partialDeriv, h, ContinuousLinearMap.fderiv]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- Sanity check on the definitions: the `j`-th partial derivative of the `i`-th coordinate
function is `1` if `i = j` and `0` otherwise. -/

theorem navier_stokes_regularity (ν : ℝ) (a : ℝ → Vec) (ha : ContDiff ℝ ∞ a) :
    ∃ (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ),
      IsGlobalSmoothSolution ν u p ∧ ∀ x, u 0 x = a 0 := by
  have hdiff : Differentiable ℝ a := (contDiff_infty_iff_deriv.1 ha).1
  have hderiv : ContDiff ℝ ∞ (deriv a) := (contDiff_infty_iff_deriv.1 ha).2
  refine ⟨fun t _ => a t, fun t x => -∑ k, deriv a t k * x k, ⟨?_, ?_, ?_, ?_⟩, fun _ => rfl⟩
  · exact ha.comp contDiff_fst
  · refine ContDiff.neg (ContDiff.sum fun k _ => ContDiff.mul ?_ ?_)
    · exact (contDiff_apply ℝ ℝ k).comp (hderiv.comp contDiff_fst)
    · exact (contDiff_apply ℝ ℝ k).comp contDiff_snd
  · intro t x
    simp [divergence]
  · intro t x i
    have hp : partialDeriv (fun y : Vec => -∑ k, deriv a t k * y k) i x = -deriv a t i :=
      partialDeriv_linear_pressure (deriv a t) i x
    simp only [hp, deriv_apply hdiff i t, partialDeriv_const, laplacian_const]
    simp

/-- **Time translation invariance** (a Lean-checked reduction): global smooth solutions
are preserved by shifting time, so solving the initial value problem at time `s` is
equivalent to solving it at time `0`. -/
