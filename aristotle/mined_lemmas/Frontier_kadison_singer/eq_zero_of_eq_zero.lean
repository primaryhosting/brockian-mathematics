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


lemma eq_zero_of_eq_zero (h : IsState phi) {y : A} (hy : phi (star y * y) = 0) (x : A) :
    phi (star y * x) = 0 := by
  rw [← h.conj_symm x y]
  suffices hu0 : phi (star x * y) = 0 by simp [hu0]
  set u : ℂ := phi (star x * y) with hu
  have hkey : ∀ s : ℝ, 0 ≤ (phi (star x * x)).re - 2 * s * Complex.normSq u := by
    intro s
    have hre := h.re_nonneg (x + (-(s : ℂ) * (starRingEnd ℂ) u) • y)
    rw [expand, hy, ← h.conj_symm x y, ← hu] at hre
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, add_zero, sub_zero, neg_zero, Complex.normSq_apply] at hre ⊢
    nlinarith [hre]
  by_contra hne
  have hpos : 0 < Complex.normSq u := by
    rcases (Complex.normSq_nonneg u).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (Complex.normSq_eq_zero.mp h'.symm) hne
  have h2 := hkey (((phi (star x * x)).re + 1) / (2 * Complex.normSq u))
  rw [show 2 * (((phi (star x * x)).re + 1) / (2 * Complex.normSq u)) * Complex.normSq u
      = (phi (star x * x)).re + 1 by field_simp] at h2
  linarith

/-- If a state takes the value `1` on a projection `p`, then it is supported on `p`:
`phi a = phi (p * a * p)` for every `a`. -/
