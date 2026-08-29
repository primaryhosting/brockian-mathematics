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

/-
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian
namespace RiemannScaffold

/-- A *Brockian system* for a function `f : ℂ → ℂ` on a complex inner product space `H`.

This is a Hilbert–Pólya style structure: a symmetric (formally self-adjoint) linear operator
`T` on `H` together with a spectral dictionary saying that every zero `ρ` of `f` is of the
form `ρ = 1/2 + λ * I` for some *eigenvalue* `λ` of `T`.

Note that no hypothesis is imposed on `f` itself; all the content is in the operator `T` and
in the spectral dictionary `hilbert_polya`. -/
structure BrockianSystem (f : ℂ → ℂ) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The Hilbert–Pólya operator of the system. -/
  T : H →ₗ[ℂ] H
  /-- `T` is symmetric (formally self-adjoint) for the inner product of `H`. -/
  symmetric : ∀ x y : H, inner ℂ (T x) y = inner ℂ x (T y)
  /-- Spectral dictionary: each zero of `f` sits at `1/2 + λ * I` for an eigenvalue `λ` of `T`. -/
  hilbert_polya : ∀ ρ : ℂ, f ρ = 0 →
    ∃ lam : ℂ, ∃ v : H, v ≠ 0 ∧ T v = lam • v ∧ ρ = 1 / 2 + lam * Complex.I

variable {f : ℂ → ℂ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Eigenvalues of a symmetric operator on a complex inner product space are real. -/

noncomputable def exampleSystem (t : ℝ) :
    BrockianSystem (fun s : ℂ => s - (1 / 2 + (t : ℂ) * Complex.I)) ℂ where
  T := (t : ℂ) • LinearMap.id
  symmetric := by
    intro x y
    simp only [LinearMap.smul_apply, LinearMap.id_apply, RCLike.inner_apply, smul_eq_mul,
      map_mul, Complex.conj_ofReal]
    ring
  hilbert_polya := by
    intro ρ hρ
    refine ⟨(t : ℂ), 1, one_ne_zero, ?_, ?_⟩
    · simp [smul_eq_mul]
    · have : ρ = 1 / 2 + (t : ℂ) * Complex.I := by
        have := sub_eq_zero.mp hρ
        simpa using this
      simpa using this

/-- Non-vacuity: for every real `t`, some function with a zero at `1/2 + t*I` carries a
Brockian system. -/
