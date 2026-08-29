import Mathlib

/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped NNReal
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

namespace Frontier

/-! ## The tilt

For a multiplicative monoid `R` and an exponent `p`, the *tilt* of `R` is the inverse limit
`lim_{x ↦ xᵖ} R`, realised as the monoid of sequences `(x₀, x₁, x₂, …)` with `xₙ₊₁ᵖ = xₙ`.
For a perfectoid field `K` this is Scholze's `K♭` (described through its multiplicative
monoid; in characteristic `p` the addition is the pointwise one). -/
structure Tilt (R : Type*) [Monoid R] (p : ℕ) where
  /-- The `n`-th component of a compatible system of `p`-power roots. -/
  coeff : ℕ → R
  /-- Compatibility: the `(n+1)`-st component is a `p`-th root of the `n`-th one. -/
  pow_coeff_succ : ∀ n : ℕ, coeff (n + 1) ^ p = coeff n

namespace Tilt

variable {R : Type*} {p : ℕ}

@[ext]

theorem ext [Monoid R] {f g : Tilt R p} (h : ∀ n, f.coeff n = g.coeff n) : f = g := by
  cases f; cases g
  simp only [Tilt.mk.injEq]
  exact funext h

instance [CommMonoid R] : CommMonoid (Tilt R p) where
  mul f g :=
    ⟨fun n => f.coeff n * g.coeff n, by
      intro n
      rw [mul_pow, f.pow_coeff_succ, g.pow_coeff_succ]⟩
  one := ⟨fun _ => 1, by intro n; simp⟩
  mul_assoc f g h := by ext n; exact mul_assoc _ _ _
  one_mul f := by ext n; exact one_mul _
  mul_one f := by ext n; exact mul_one _
  mul_comm f g := by ext n; exact mul_comm _ _

@[simp]
