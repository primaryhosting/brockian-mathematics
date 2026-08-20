/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to come before any module docstring, so the header
-- above is reproduced verbatim as the module docstring immediately after the imports.)

import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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
set_option pp.piBinderTypes true
set_option pp.letVarTypes true
set_option pp.funBinderTypes true

set_option grind.warning false

namespace Frontier

open scoped ComplexOrder InnerProductSpace

/-! ## States on a unital ⋆-algebra over `ℂ` -/

/-- A *state* on a unital `ℂ`-⋆-algebra `A`: a positive, normalized linear functional. -/
structure IsState {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    (phi : A →ₗ[ℂ] ℂ) : Prop where
  /-- Positivity: `phi (a⋆ * a)` is a nonnegative real number. -/
  nonneg : ∀ a : A, 0 ≤ phi (star a * a)
  /-- Normalization. -/
  map_one : phi 1 = 1

namespace IsState

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] {phi : A →ₗ[ℂ] ℂ}


lemma conj_symm (h : IsState phi) (x y : A) :
    (starRingEnd ℂ) (phi (star x * y)) = phi (star y * x) := by
  set u : ℂ := phi (star x * y) with hu
  set v : ℂ := phi (star y * x) with hv
  have key : ∀ t : ℂ, (t * u + (starRingEnd ℂ) t * v).im = 0 := by
    intro t
    have h1 := h.im_eq_zero (x + t • y)
    rw [expand t x y, ← hu, ← hv] at h1
    have h2 := h.im_eq_zero x
    have h3 := h.im_eq_zero y
    simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, h2, h3] at h1 ⊢
    nlinarith [h1]
  have k1 := key 1
  have k2 := key Complex.I
  simp only [one_mul, Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.conj_I, Complex.neg_re,
    Complex.neg_im] at k1 k2
  apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im] <;> linarith

/-- A state is ⋆-preserving. -/
