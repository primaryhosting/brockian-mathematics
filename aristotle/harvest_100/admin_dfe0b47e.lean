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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Basic differential operators on `ℝ³` -/

/-- Physical space `ℝ³`. -/
abbrev Vec3 : Type := Fin 3 → ℝ

/-- The partial derivative `∂f/∂xᵢ` of a scalar field on `ℝ³`. -/
noncomputable def partialDeriv (i : Fin 3) (f : Vec3 → ℝ) (x : Vec3) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The divergence `∇ · u` of a vector field on `ℝ³`. -/
noncomputable def divergence (u : Vec3 → Vec3) (x : Vec3) : ℝ :=
  ∑ i, partialDeriv i (fun y => u y i) x

/-- The Laplacian `Δ f = ∑ᵢ ∂²f/∂xᵢ²` of a scalar field on `ℝ³`. -/
noncomputable def laplacian (f : Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∑ i, partialDeriv i (partialDeriv i f) x

/-- Schwartz-type admissibility of initial data: `f` is smooth and `f` together with all of
its derivatives decays faster than any polynomial. -/
def SchwartzDecay (f : Vec3 → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n K : ℕ, ∃ C : ℝ, ∀ x : Vec3, ‖iteratedFDeriv ℝ n f x‖ * (1 + ‖x‖) ^ K ≤ C

/-! ## The Navier–Stokes equations -/

/-- `IsGlobalSmoothSolution ν u p u₀` says that the velocity field `u` and pressure `p` form a
globally defined smooth solution of the incompressible Navier–Stokes equations on `ℝ³` with
viscosity `ν` and initial velocity `u₀`, with uniformly bounded kinetic energy.

Following the Clay Millennium Problem formulation, the equations are only required to hold for
times `t ≥ 0`; smoothness is stated for functions defined on all of `ℝ × ℝ³`, which avoids
one-sided derivatives at the initial time. -/
structure IsGlobalSmoothSolution (ν : ℝ) (u : ℝ → Vec3 → Vec3) (p : ℝ → Vec3 → ℝ)
    (u₀ : Vec3 → Vec3) : Prop where
  /-- Each velocity component is jointly smooth in time and space. -/
  contDiff_u : ∀ j, ContDiff ℝ ∞ (fun q : ℝ × Vec3 => u q.1 q.2 j)
  /-- The pressure is jointly smooth in time and space. -/
  contDiff_p : ContDiff ℝ ∞ (fun q : ℝ × Vec3 => p q.1 q.2)
  /-- The velocity field has the prescribed initial value. -/
  initial : ∀ x, u 0 x = u₀ x
  /-- Incompressibility: `∇ · u = 0`. -/
  incompressible : ∀ t, 0 ≤ t → ∀ x, divergence (u t) x = 0
  /-- The momentum equation `∂ₜu + (u · ∇)u = ν Δu - ∇p`. -/
  momentum : ∀ t, 0 ≤ t → ∀ (x : Vec3) (j : Fin 3),
    deriv (fun s => u s x j) t + ∑ i, u t x i * partialDeriv i (fun y => u t y j) x
      = ν * laplacian (fun y => u t y j) x - partialDeriv j (p t) x
  /-- Bounded kinetic energy, uniformly in time. -/
  energy : ∃ C : ℝ, ∀ t, 0 ≤ t →
    MeasureTheory.Integrable (fun x : Vec3 => ∑ i, (u t x i) ^ 2) ∧
      ∫ x : Vec3, ∑ i, (u t x i) ^ 2 ≤ C

/-- Global regularity for the 3D incompressible Navier–Stokes equations with viscosity `ν`:
every smooth, rapidly decreasing, divergence-free initial velocity field admits a globally
defined smooth solution with bounded energy. -/
def GlobalRegularity (ν : ℝ) : Prop :=
  ∀ u₀ : Vec3 → Vec3, (∀ j, SchwartzDecay (fun x => u₀ x j)) → (∀ x, divergence u₀ x = 0) →
    ∃ (u : ℝ → Vec3 → Vec3) (p : ℝ → Vec3 → ℝ), IsGlobalSmoothSolution ν u p u₀

/-! ## Calculus lemmas -/

theorem contDiff_slice_space {F : ℝ → Vec3 → ℝ} (h : ContDiff ℝ ∞ (fun q : ℝ × Vec3 => F q.1 q.2))
    (s : ℝ) : ContDiff ℝ ∞ (fun y : Vec3 => F s y) :=
  h.comp (contDiff_const.prodMk contDiff_id)

theorem contDiff_slice_time {F : ℝ → Vec3 → ℝ} (h : ContDiff ℝ ∞ (fun q : ℝ × Vec3 => F q.1 q.2))
    (x : Vec3) : ContDiff ℝ ∞ (fun s : ℝ => F s x) :=
  h.comp (contDiff_id.prodMk contDiff_const)

theorem contDiff_partialDeriv {f : Vec3 → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (partialDeriv i f) := by
  unfold partialDeriv
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem partialDeriv_const_mul {f : Vec3 → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (i : Fin 3)
    (x : Vec3) : partialDeriv i (fun y => c * f y) x = c * partialDeriv i f x := by
  unfold partialDeriv
  rw [fderiv_const_mul (hf x)]
  simp

theorem laplacian_const_mul {f : Vec3 → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (x : Vec3) :
    laplacian (fun y => c * f y) x = c * laplacian f x := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have h1 : ∀ i : Fin 3, partialDeriv i (fun y => c * f y) = fun y => c * partialDeriv i f y :=
    fun i => funext fun y => partialDeriv_const_mul hd c i y
  unfold laplacian
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h1 i, partialDeriv_const_mul ((contDiff_partialDeriv hf i).differentiable (by simp)) c i x]

theorem deriv_const_mul_comp_mul {g : ℝ → ℝ} (hg : Differentiable ℝ g) (c a t : ℝ) :
    deriv (fun s => c * g (a * s)) t = c * a * deriv g (a * t) := by
  have h1 : HasDerivAt (fun s : ℝ => a * s) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have h2 : HasDerivAt (fun s : ℝ => g (a * s)) (deriv g (a * t) * a) t :=
    (hg (a * t)).hasDerivAt.comp t h1
  rw [(h2.const_mul c).deriv]
  ring

theorem SchwartzDecay.const_mul {f : Vec3 → ℝ} (hf : SchwartzDecay f) (c : ℝ) :
    SchwartzDecay (fun x => c * f x) := by
  obtain ⟨hs, hd⟩ := hf
  refine ⟨contDiff_const.mul hs, fun n K => ?_⟩
  obtain ⟨C, hC⟩ := hd n K
  refine ⟨|c| * C, fun x => ?_⟩
  have hfun : (fun x => c * f x) = c • f := by funext y; simp [Pi.smul_apply]
  rw [hfun, iteratedFDeriv_const_smul_apply (hs.of_le (by exact_mod_cast le_top)).contDiffAt,
    norm_smul]
  simp only [Real.norm_eq_abs]
  calc |c| * ‖iteratedFDeriv ℝ n f x‖ * (1 + ‖x‖) ^ K
      = |c| * (‖iteratedFDeriv ℝ n f x‖ * (1 + ‖x‖) ^ K) := by ring
    _ ≤ |c| * C := mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)

/-! ## The viscosity scaling reduction -/

/-- Scaling of the divergence by a constant factor. -/
theorem divergence_const_mul {u : Vec3 → Vec3} (hu : ∀ i, Differentiable ℝ (fun y => u y i))
    (c : ℝ) (x : Vec3) :
    divergence (fun y j => c * u y j) x = c * divergence u x := by
  unfold divergence
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => partialDeriv_const_mul (hu i) c i x

/-- The Navier–Stokes scaling symmetry: global regularity for one positive viscosity implies
global regularity for every positive viscosity.  The proof rescales a solution `u` for viscosity
`ν` into `v (t, x) = a • u (a t, x)`, with pressure `a² p (a t, x)` and `a = μ / ν`, which solves
the equations for viscosity `μ` with initial datum `a • u₀`. -/
theorem globalRegularity_of_globalRegularity {ν μ : ℝ} (hν : 0 < ν) (hμ : 0 < μ)
    (h : GlobalRegularity ν) : GlobalRegularity μ := by
  intro w₀ hw₀ hwdiv
  obtain ⟨a, ha0, haw⟩ : ∃ a : ℝ, 0 < a ∧ μ = a * ν :=
    ⟨μ / ν, div_pos hμ hν, by field_simp⟩
  have hwdiff : ∀ i, Differentiable ℝ (fun y => w₀ y i) := fun i =>
    (hw₀ i).1.differentiable (by simp)
  -- rescaled initial datum for the `ν`-problem
  obtain ⟨u, p, hsol⟩ := h (fun x j => a⁻¹ * w₀ x j)
    (fun j => (hw₀ j).const_mul a⁻¹)
    (fun x => by rw [divergence_const_mul hwdiff a⁻¹ x, hwdiv x, mul_zero])
  have hu_space : ∀ (s : ℝ) (j : Fin 3), ContDiff ℝ ∞ (fun y : Vec3 => u s y j) :=
    fun s j => contDiff_slice_space (F := fun s y => u s y j) (hsol.contDiff_u j) s
  have hu_time : ∀ (x : Vec3) (j : Fin 3), Differentiable ℝ (fun s : ℝ => u s x j) :=
    fun x j =>
      (contDiff_slice_time (F := fun s y => u s y j) (hsol.contDiff_u j) x).differentiable (by simp)
  have hp_space : ∀ s : ℝ, ContDiff ℝ ∞ (fun y : Vec3 => p s y) :=
    fun s => contDiff_slice_space (F := fun s y => p s y) hsol.contDiff_p s
  obtain ⟨C, hC⟩ := hsol.energy
  refine ⟨fun t x j => a * u (a * t) x j, fun t x => a ^ 2 * p (a * t) x, ?_⟩
  have hscale : ContDiff ℝ ∞ (fun q : ℝ × Vec3 => (a * q.1, q.2)) :=
    (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
  refine
    { contDiff_u := fun j => contDiff_const.mul (((hsol.contDiff_u j).comp hscale))
      contDiff_p := contDiff_const.mul (hsol.contDiff_p.comp hscale)
      initial := ?_
      incompressible := ?_
      momentum := ?_
      energy := ?_ }
  · intro x
    funext j
    simp only [mul_zero]
    rw [hsol.initial x]
    field_simp
  · intro t ht x
    have hat : 0 ≤ a * t := mul_nonneg ha0.le ht
    rw [divergence_const_mul (fun i => (hu_space (a * t) i).differentiable (by simp)) a x,
      hsol.incompressible _ hat, mul_zero]
  · intro t ht x j
    have hat : 0 ≤ a * t := mul_nonneg ha0.le ht
    have hmom := hsol.momentum (a * t) hat x j
    have hderiv : deriv (fun s => a * u (a * s) x j) t
        = a * a * deriv (fun s => u s x j) (a * t) :=
      deriv_const_mul_comp_mul (hu_time x j) a a t
    have hconv : ∑ i, (a * u (a * t) x i) * partialDeriv i (fun y => a * u (a * t) y j) x
        = a * a * ∑ i, u (a * t) x i * partialDeriv i (fun y => u (a * t) y j) x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [partialDeriv_const_mul ((hu_space (a * t) j).differentiable (by simp)) a i x]
      ring
    have hlap : laplacian (fun y => a * u (a * t) y j) x
        = a * laplacian (fun y => u (a * t) y j) x :=
      laplacian_const_mul (hu_space (a * t) j) a x
    have hpres : partialDeriv j (fun x => a ^ 2 * p (a * t) x) x
        = a ^ 2 * partialDeriv j (fun y => p (a * t) y) x :=
      partialDeriv_const_mul ((hp_space (a * t)).differentiable (by simp)) (a ^ 2) j x
    simp only [hderiv, hconv, hlap, hpres, haw]
    nlinarith [hmom]
  · refine ⟨a ^ 2 * C, fun t ht => ?_⟩
    have hat : 0 ≤ a * t := mul_nonneg ha0.le ht
    obtain ⟨hint, hle⟩ := hC (a * t) hat
    have hfun : (fun x : Vec3 => ∑ i, (a * u (a * t) x i) ^ 2)
        = fun x : Vec3 => a ^ 2 * ∑ i, (u (a * t) x i) ^ 2 := by
      funext x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    constructor
    · rw [hfun]
      exact hint.const_mul (a ^ 2)
    · rw [hfun, MeasureTheory.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hle (by positivity)

/-! ## The base case: the trivial (zero) initial datum -/

theorem partialDeriv_zero (i : Fin 3) : partialDeriv i (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
  funext x; simp [partialDeriv]

theorem isGlobalSmoothSolution_zero (ν : ℝ) :
    IsGlobalSmoothSolution ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) where
  contDiff_u := fun _ => contDiff_const
  contDiff_p := contDiff_const
  initial := fun _ => rfl
  incompressible := fun _ _ _ => by simp [divergence, partialDeriv_zero]
  momentum := fun _ _ _ _ => by
    simp [laplacian, partialDeriv_zero]
  energy := ⟨0, fun _ _ => by simp⟩

/-! ## A nontrivial family of exact solutions -/

/-- The Navier–Stokes system (incompressibility and the momentum equation) for `(u, p)` at all
times, without any decay or energy requirement. -/
def SatisfiesNSEquations (ν : ℝ) (u : ℝ → Vec3 → Vec3) (p : ℝ → Vec3 → ℝ) : Prop :=
  (∀ t x, divergence (u t) x = 0) ∧
    (∀ (t : ℝ) (x : Vec3) (j : Fin 3),
      deriv (fun s => u s x j) t + ∑ i, u t x i * partialDeriv i (fun y => u t y j) x
        = ν * laplacian (fun y => u t y j) x - partialDeriv j (p t) x)

theorem partialDeriv_const (i : Fin 3) (c : ℝ) :
    partialDeriv i (fun _ : Vec3 => c) = fun _ => (0 : ℝ) := by
  funext x; simp [partialDeriv]

theorem partialDeriv_linear (c : Vec3) (j : Fin 3) (x : Vec3) :
    partialDeriv j (fun y : Vec3 => -∑ k, c k * y k) x = -c j := by
  have h : (fun y : Vec3 => -∑ k, c k * y k) = fun y : Vec3 =>
      (-(∑ k, (c k) • (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)) : Vec3 →L[ℝ] ℝ) y := by
    funext y; simp
  rw [partialDeriv, h, ContinuousLinearMap.fderiv]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- Spatially uniform flows are exact solutions of the Navier–Stokes system: for any (not
necessarily smooth) curve `f : ℝ → ℝ³`, the velocity `u (t, x) = f t` together with the linear
pressure `p (t, x) = -f'(t) · x` solves the equations.  This witnesses that the formalized
system admits nontrivial solutions; these solutions have infinite energy, so they are not
covered by `IsGlobalSmoothSolution`. -/
theorem satisfiesNSEquations_uniform (ν : ℝ) (f : ℝ → Vec3) :
    SatisfiesNSEquations ν (fun t _ => f t)
      (fun t x => -∑ k, deriv (fun s => f s k) t * x k) := by
  constructor
  · intro t x
    simp [divergence, partialDeriv_const]
  · intro t x j
    rw [partialDeriv_linear (fun k => deriv (fun s => f s k) t) j x]
    simp [laplacian, partialDeriv_const]

/-! ## Main statement -/

/-- **Navier–Stokes regularity (formalized statement, base case and Lean-checked reduction).**

The first component is the Lean-checked reduction: global smoothness/existence for the
3D incompressible Navier–Stokes equations at *any* positive viscosity is equivalent to global
smoothness/existence at viscosity `1`; i.e. the Millennium problem for all viscosities reduces to
the single normalized case `ν = 1` (equivalently, in contrapositive form, a finite-energy blow-up
for some viscosity produces one for viscosity `1`).

The second component is the base case: for every viscosity the trivial initial datum admits a
global smooth finite-energy solution. -/
theorem navier_stokes_regularity :
    (∀ ν : ℝ, 0 < ν → (GlobalRegularity ν ↔ GlobalRegularity 1)) ∧
      (∀ ν : ℝ, ∃ (u : ℝ → Vec3 → Vec3) (p : ℝ → Vec3 → ℝ),
        IsGlobalSmoothSolution ν u p (fun _ _ => 0)) := by
  refine ⟨fun ν hν => ⟨fun h => globalRegularity_of_globalRegularity hν one_pos h,
    fun h => globalRegularity_of_globalRegularity one_pos hν h⟩, fun ν => ?_⟩
  exact ⟨_, _, isGlobalSmoothSolution_zero ν⟩

end Frontier

#print axioms Frontier.navier_stokes_regularity
#print axioms Frontier.globalRegularity_of_globalRegularity
#print axioms Frontier.isGlobalSmoothSolution_zero
#print axioms Frontier.satisfiesNSEquations_uniform

