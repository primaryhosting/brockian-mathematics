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

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate Real
open LinearPMap Submodule

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Essential self-adjointness -/

section Abstract

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A densely defined operator `A` is *essentially self-adjoint* when it is symmetric and its
adjoint is self-adjoint (equivalently, its closure is self-adjoint; equivalently, it has a
unique self-adjoint extension, see `unique_selfAdjoint_extension`). -/

theorem trigPolyC_ode (V₀ : ℝ) (g : ℤ → ℂ) (s : Finset ℤ) (x : ℝ) :
    -(deriv (deriv fun y : ℝ => trigPolyC T g s (y : AddCircle T)) x)
        + (V₀ : ℂ) * trigPolyC T g s (x : AddCircle T)
      = trigPolyC T (fun n => (eig T V₀ n : ℂ) * g n) s (x : AddCircle T) := by
  have hfun : (fun y : ℝ => trigPolyC T g s (y : AddCircle T))
      = fun y : ℝ => ∑ n ∈ s, g n * fourier n (y : AddCircle T) := by
    funext y; simp [trigPolyC]
  have hfn : ∀ (c : ℤ → ℂ), (∑ n ∈ s, fun z : ℝ => c n * fourier n (z : AddCircle T))
      = fun z : ℝ => ∑ n ∈ s, c n * fourier n (z : AddCircle T) := by
    intro c; funext z; simp
  have D1 : ∀ y : ℝ, HasDerivAt (fun z : ℝ => ∑ n ∈ s, g n * fourier n (z : AddCircle T))
      (∑ n ∈ s, g n * (2 * π * Complex.I * n / T * fourier n (y : AddCircle T))) y := by
    intro y
    have h := HasDerivAt.sum (u := s) (A := fun n (z : ℝ) => g n * fourier n (z : AddCircle T))
      (A' := fun n => g n * (2 * π * Complex.I * n / T * fourier n (y : AddCircle T)))
      (fun n _ => (hasDerivAt_fourier T n y).const_mul (g n))
    rwa [hfn g] at h
  have hd1 : (deriv fun z : ℝ => ∑ n ∈ s, g n * fourier n (z : AddCircle T))
      = fun y : ℝ => ∑ n ∈ s, g n * (2 * π * Complex.I * n / T * fourier n (y : AddCircle T)) :=
    funext fun y => (D1 y).deriv
  have D2 : HasDerivAt
      (fun z : ℝ => ∑ n ∈ s, g n * (2 * π * Complex.I * n / T * fourier n (z : AddCircle T)))
      (∑ n ∈ s, g n * (2 * π * Complex.I * n / T *
        (2 * π * Complex.I * n / T * fourier n (x : AddCircle T)))) x := by
    have h := HasDerivAt.sum (u := s)
      (A := fun n (z : ℝ) => g n * (2 * π * Complex.I * n / T * fourier n (z : AddCircle T)))
      (A' := fun n => g n * (2 * π * Complex.I * n / T *
        (2 * π * Complex.I * n / T * fourier n (x : AddCircle T))))
      (fun n _ => ((hasDerivAt_fourier T n x).const_mul
        (2 * π * Complex.I * n / T)).const_mul (g n))
    have hfn2 : (∑ n ∈ s, fun z : ℝ =>
        g n * (2 * π * Complex.I * n / T * fourier n (z : AddCircle T)))
        = fun z : ℝ => ∑ n ∈ s, g n * (2 * π * Complex.I * n / T * fourier n (z : AddCircle T)) := by
      funext z; simp
    rwa [hfn2] at h
  rw [hfun, hd1, D2.deriv]
  simp only [trigPolyC, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [eig]
  push_cast
  linear_combination (-(g n) * ((2 * π * (n : ℂ) / T) ^ 2) * fourier n (x : AddCircle T)) *
    Complex.I_sq

/-- **The minimal Schrödinger operator acts as the differential expression `-d²/dx² + V₀`.**
For a trigonometric polynomial `u` in the domain, with continuous (indeed smooth) representative
`F`, the image `schrodingerMin T V₀ u` is represented by the continuous function `G` obtained from
`F` by the classical Schrödinger differential expression. -/
