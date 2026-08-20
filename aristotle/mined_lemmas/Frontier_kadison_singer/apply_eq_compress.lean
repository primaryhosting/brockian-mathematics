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


lemma apply_eq_compress (h : IsState phi) {p : A} (hp : star p = p) (hp2 : p * p = p)
    (h1 : phi p = 1) (a : A) : phi a = phi (p * a * p) := by
  set q : A := 1 - p with hq
  have hqs : star q = q := by simp [hq, hp]
  have hq2 : q * q = q := by simp [hq, sub_mul, mul_sub, hp2]
  have hq0 : phi q = 0 := by simp [hq, map_sub, h.map_one, h1]
  have hqq : phi (star q * q) = 0 := by rw [hqs, hq2, hq0]
  have hleft : ∀ x : A, phi (q * x) = 0 := by
    intro x
    have := h.eq_zero_of_eq_zero hqq x
    rwa [hqs] at this
  have hright : ∀ x : A, phi (x * q) = 0 := by
    intro x
    have hs : phi (star (x * q)) = 0 := by
      rw [star_mul, hqs]
      exact hleft _
    rw [h.star_apply] at hs
    simpa using congrArg (starRingEnd ℂ) hs
  have e1 : ∀ x : A, phi x = phi (p * x) := by
    intro x
    have hx : p * x = x - q * x := by simp [hq, sub_mul]
    rw [hx, map_sub, hleft, sub_zero]
  have e2 : ∀ x : A, phi x = phi (x * p) := by
    intro x
    have hx : x * p = x - x * q := by simp [hq, mul_sub]
    rw [hx, map_sub, hright, sub_zero]
  rw [e1 a, e2 (p * a)]

end IsState

/-! ## Rank-one projections and diagonal operators -/

section RankOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The orthogonal projection onto the line spanned by a unit vector `e`, as a bounded
operator: `x ↦ ⟪e, x⟫ • e`. -/
