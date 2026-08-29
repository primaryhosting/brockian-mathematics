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

