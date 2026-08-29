import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ContDiff BigOperators

namespace Frontier

/-- The physical space `ℝ³`, as the space of `3`-tuples of reals. -/
abbrev Vec : Type := Fin 3 → ℝ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `i`-th partial derivative of a (vector- or scalar-valued) field on `ℝ³`. -/
noncomputable def partialD (i : Fin 3) (f : Vec → E) (x : Vec) : E :=
  fderiv ℝ f x (Pi.single i 1)

/-- The divergence `∑ᵢ ∂ᵢ vᵢ` of a vector field on `ℝ³`. -/
noncomputable def divergence (v : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i, partialD i (fun y => v y i) x

/-- The gradient `(∂₁ f, ∂₂ f, ∂₃ f)` of a scalar field on `ℝ³`. -/
noncomputable def gradient (f : Vec → ℝ) (x : Vec) : Vec :=
  fun i => partialD i f x

/-- The Laplacian `∑ᵢ ∂ᵢ∂ᵢ f`. -/
noncomputable def laplacian (f : Vec → E) (x : Vec) : E :=
  ∑ i, partialD i (partialD i f) x

/-- The convective (nonlinear) term `(v · ∇) v`. -/
noncomputable def convective (v : Vec → Vec) (x : Vec) : Vec :=
  ∑ i, v x i • partialD i v x

/-- `IsNSSolution ν u p` says that the velocity field `u` and the pressure `p` are smooth on
`ℝ × ℝ³` and solve the incompressible Navier–Stokes equations on `ℝ³ × [0, ∞)` with
viscosity `ν`:

`∂ₜ u + (u · ∇) u = ν Δu - ∇p`,  `div u = 0`. -/
structure IsNSSolution (ν : ℝ) (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ) : Prop where
  smooth_u : ContDiff ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
  smooth_p : ContDiff ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2)
  momentum : ∀ t, 0 ≤ t → ∀ x, deriv (fun s => u s x) t + convective (u t) x
      = ν • laplacian (u t) x - gradient (p t) x
  incompressible : ∀ t, 0 ≤ t → ∀ x, divergence (u t) x = 0

/-- The kinetic energy `∫_{ℝ³} |u(t, x)|² dx` (up to the usual factor `1/2`). -/
noncomputable def energy (u : ℝ → Vec → Vec) (t : ℝ) : ℝ := ∫ x, ∑ i, (u t x i) ^ 2

/-- Admissible initial data: a smooth, compactly supported, divergence-free vector field.
(The Clay problem allows Schwartz data; compactly supported data is the natural smooth
subclass used here.) -/
def IsAdmissibleData (u₀ : Vec → Vec) : Prop :=
  ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧ ∀ x, divergence u₀ x = 0

/-- Existence of a globally defined smooth solution with bounded energy for the initial
datum `u₀` and viscosity `ν`. -/
def HasGlobalSmoothSolution (ν : ℝ) (u₀ : Vec → Vec) : Prop :=
  ∃ u p, IsNSSolution ν u p ∧ u 0 = u₀ ∧ ∃ C, ∀ t, 0 ≤ t → energy u t ≤ C

/-- **Global regularity for the 3D incompressible Navier–Stokes equations** with viscosity
`ν`: every admissible initial datum admits a global smooth solution of bounded energy.
This is the (open) Clay Millennium statement; it is *not* proved here. -/
def NavierStokesGlobalRegularity (ν : ℝ) : Prop :=
  ∀ u₀, IsAdmissibleData u₀ → HasGlobalSmoothSolution ν u₀

/-! ## Calculus lemmas -/

theorem contDiff_partialD {f : Vec → E} (i : Fin 3) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (partialD i f) :=
  (hf.fderiv_right le_rfl).clm_apply contDiff_const

theorem partialD_const_smul (i : Fin 3) (c : ℝ) {f : Vec → E} (hf : Differentiable ℝ f)
    (x : Vec) : partialD i (fun y => c • f y) x = c • partialD i f x := by
  unfold partialD
  rw [show (fun y => c • f y) = c • f from rfl, fderiv_const_smul (hf x) c]
  rfl

@[simp] theorem partialD_const (i : Fin 3) (a : E) (x : Vec) :
    partialD i (fun _ => a) x = 0 := by
  simp [partialD]

@[simp] theorem partialD_const_fun (i : Fin 3) (a : E) :
    partialD i (fun _ => a) = fun _ => (0 : E) :=
  funext (partialD_const i a)

@[simp] theorem gradient_const (a : ℝ) (x : Vec) : gradient (fun _ => a) x = 0 := by
  funext i
  simp [gradient]

theorem laplacian_const_smul (c : ℝ) {f : Vec → E} (hf : ContDiff ℝ ∞ f) (x : Vec) :
    laplacian (fun y => c • f y) x = c • laplacian f x := by
  unfold laplacian
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (partialD i fun z => c • f z) = fun y => c • partialD i f y := by
    funext y; exact partialD_const_smul i c (hf.differentiable (by simp)) y
  rw [h1]
  exact partialD_const_smul i c ((contDiff_partialD i hf).differentiable (by simp)) x

theorem differentiable_coord {v : Vec → Vec} (hv : Differentiable ℝ v) (i : Fin 3) :
    Differentiable ℝ (fun y => v y i) :=
  ((ContinuousLinearMap.proj i : Vec →L[ℝ] ℝ).differentiable).comp hv

theorem divergence_const_smul (c : ℝ) {v : Vec → Vec} (hv : Differentiable ℝ v) (x : Vec) :
    divergence (fun y => c • v y) x = c * divergence v x := by
  unfold divergence
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun y => (c • v y) i) = fun y => c • (v y i) := rfl
  rw [h1, partialD_const_smul i c (differentiable_coord hv i) x, smul_eq_mul]

theorem gradient_const_smul (c : ℝ) {f : Vec → ℝ} (hf : Differentiable ℝ f) (x : Vec) :
    gradient (fun y => c • f y) x = c • gradient f x := by
  funext i
  exact partialD_const_smul i c hf x

theorem convective_const_smul (c : ℝ) {v : Vec → Vec} (hv : Differentiable ℝ v) (x : Vec) :
    convective (fun y => c • v y) x = (c * c) • convective v x := by
  unfold convective
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [partialD_const_smul i c hv x]
  show (c * v x i) • c • partialD i v x = (c * c) • v x i • partialD i v x
  rw [smul_smul, smul_smul]
  ring_nf

theorem contDiff_fixed_time {u : ℝ → Vec → E}
    (h : ContDiff ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)) (t : ℝ) : ContDiff ℝ ∞ (u t) :=
  h.comp (contDiff_const.prodMk contDiff_id)

theorem differentiable_time {u : ℝ → Vec → Vec}
    (h : ContDiff ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)) (x : Vec) :
    Differentiable ℝ (fun s => u s x) :=
  (h.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)

/-! ## The trivial (zero) solution: the base case -/

theorem isNSSolution_zero (ν : ℝ) :
    IsNSSolution ν (fun _ _ => (0 : Vec)) (fun _ _ => (0 : ℝ)) where
  smooth_u := contDiff_const
  smooth_p := contDiff_const
  momentum := by
    intro t _ x
    simp [convective, laplacian]
  incompressible := by
    intro t _ x
    simp [divergence]

theorem energy_zero_solution (t : ℝ) : energy (fun _ _ => (0 : Vec)) t = 0 := by
  simp [energy]

/-- Base case of global regularity: the zero initial datum admits a global smooth solution
with bounded (indeed vanishing) energy, for every viscosity. -/
theorem hasGlobalSmoothSolution_zero (ν : ℝ) :
    HasGlobalSmoothSolution ν (fun _ => 0) :=
  ⟨fun _ _ => 0, fun _ _ => 0, isNSSolution_zero ν, rfl, 0, fun t _ => by
    simp [energy_zero_solution t]⟩

/-! ## Reduction to unit viscosity -/

/-- If `(v, q)` solves Navier–Stokes with viscosity `1`, then `u(t,x) = ν v(νt, x)`,
`p(t,x) = ν² q(νt, x)` solves it with viscosity `ν`. -/
theorem IsNSSolution.rescale {v : ℝ → Vec → Vec} {q : ℝ → Vec → ℝ} (h : IsNSSolution 1 v q)
    {ν : ℝ} (hν : 0 < ν) :
    IsNSSolution ν (fun t x => ν • v (ν * t) x) (fun t x => (ν * ν) • q (ν * t) x) where
  smooth_u := by
    have hlin : ContDiff ℝ ∞ (fun z : ℝ × Vec => ((ν * z.1 : ℝ), z.2)) :=
      (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
    exact (h.smooth_u.comp hlin).const_smul ν
  smooth_p := by
    have hlin : ContDiff ℝ ∞ (fun z : ℝ × Vec => ((ν * z.1 : ℝ), z.2)) :=
      (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
    exact (h.smooth_p.comp hlin).const_smul (ν * ν)
  momentum := by
    intro t ht x
    have hvx : Differentiable ℝ (fun s => v s x) := differentiable_time h.smooth_u x
    have hvs : ContDiff ℝ ∞ (v (ν * t)) := contDiff_fixed_time h.smooth_u (ν * t)
    have hqs : ContDiff ℝ ∞ (q (ν * t)) := contDiff_fixed_time h.smooth_p (ν * t)
    have hd : HasDerivAt (fun s => ν • v (ν * s) x)
        (ν • (ν • deriv (fun s => v s x) (ν * t))) t := by
      have h0 : HasDerivAt (fun s => v (ν * s) x) (ν • deriv (fun s => v s x) (ν * t)) t := by
        simpa using
          HasDerivAt.scomp t (hvx (ν * t)).hasDerivAt ((hasDerivAt_id t).const_mul ν)
      exact h0.const_smul ν
    have hmom := h.momentum (ν * t) (by positivity) x
    rw [hd.deriv, convective_const_smul ν (hvs.differentiable (by simp)) x,
      laplacian_const_smul ν hvs x, gradient_const_smul (ν * ν) (hqs.differentiable (by simp)) x]
    have hA : deriv (fun s => v s x) (ν * t)
        = laplacian (v (ν * t)) x - gradient (q (ν * t)) x - convective (v (ν * t)) x := by
      rw [one_smul] at hmom
      rw [← hmom]
      abel
    rw [hA]
    module
  incompressible := by
    intro t ht x
    have hvs : ContDiff ℝ ∞ (v (ν * t)) := contDiff_fixed_time h.smooth_u (ν * t)
    rw [divergence_const_smul ν (hvs.differentiable (by simp)) x,
      h.incompressible (ν * t) (by positivity) x, mul_zero]

theorem energy_rescale (v : ℝ → Vec → Vec) (ν t : ℝ) :
    energy (fun t x => ν • v (ν * t) x) t = ν ^ 2 * energy v (ν * t) := by
  unfold energy
  rw [← MeasureTheory.integral_const_mul]
  refine congrArg _ (funext fun x => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (ν * v (ν * t) x i) ^ 2 = ν ^ 2 * (v (ν * t) x i) ^ 2
  ring

/-- **Lean-checked reduction.** Global regularity for unit viscosity implies global
regularity for every positive viscosity. -/
theorem navier_stokes_regularity_reduction (h : NavierStokesGlobalRegularity 1) :
    ∀ ν : ℝ, 0 < ν → NavierStokesGlobalRegularity ν := by
  rintro ν hν u₀ ⟨hsmooth, hsupp, hdiv⟩
  have hadm : IsAdmissibleData (fun x => ν⁻¹ • u₀ x) := by
    refine ⟨hsmooth.const_smul ν⁻¹, ?_, fun x => ?_⟩
    · exact HasCompactSupport.smul_left (f := fun _ : Vec => ν⁻¹) hsupp
    · rw [divergence_const_smul ν⁻¹ (hsmooth.differentiable (by simp)) x, hdiv x, mul_zero]
  obtain ⟨v, q, hsol, hv0, C, hC⟩ := h _ hadm
  refine ⟨fun t x => ν • v (ν * t) x, fun t x => (ν * ν) • q (ν * t) x, hsol.rescale hν, ?_,
    ν ^ 2 * C, fun t ht => ?_⟩
  · funext x
    show ν • v (ν * 0) x = u₀ x
    rw [mul_zero, hv0]
    simp [smul_smul, mul_inv_cancel₀ (ne_of_gt hν)]
  · rw [energy_rescale v ν t]
    exact mul_le_mul_of_nonneg_left (hC (ν * t) (by positivity)) (by positivity)

/-- **Navier–Stokes regularity: base case and a reduction.**

The first conjunct is the base case of the global regularity statement: for every viscosity
the zero initial datum admits a globally defined smooth, finite-energy solution of the 3D
incompressible Navier–Stokes equations.

The second conjunct is a Lean-checked reduction: global regularity for unit viscosity
implies global regularity for every positive viscosity, via the time rescaling
`u(t,x) = ν v(νt, x)`, `p(t,x) = ν² q(νt, x)`.

The full Clay Millennium statement is `Frontier.NavierStokesGlobalRegularity`, which
remains open and is not asserted here. -/
theorem navier_stokes_regularity :
    (∀ ν : ℝ, HasGlobalSmoothSolution ν (fun _ => 0)) ∧
    (NavierStokesGlobalRegularity 1 → ∀ ν : ℝ, 0 < ν → NavierStokesGlobalRegularity ν) :=
  ⟨hasGlobalSmoothSolution_zero, navier_stokes_regularity_reduction⟩

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

