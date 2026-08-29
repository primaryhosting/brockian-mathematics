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

theorem isUnit_of_coeff_zero_ne_zero {K : Type*} [Field K] (hp : p ≠ 0) (f : Tilt K p)
    (h : f.coeff 0 ≠ 0) : IsUnit f := by
  have hmul : f * inv f = 1 := by
    ext n
    have hne := coeff_ne_zero_of_coeff_zero_ne_zero hp f h n
    show f.coeff n * (f.coeff n)⁻¹ = 1
    rw [mul_inv_cancel₀ hne]
  exact ⟨⟨f, inv f, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

end Tilt

/-! ## Perfectoid fields -/

/-- **Perfectoid field** (Scholze): a field `K` equipped with a rank-one valuation
`v : K → ℝ≥0` such that

* `K` is complete for the `v`-topology;
* `v` is nontrivial and non-discrete (its value group is dense);
* the residue characteristic is `p`, i.e. `v p < 1`;
* Frobenius is surjective on `𝒪_K / p`.
-/
structure IsPerfectoidField (p : ℕ) (K : Type*) [Field K] (v : Valuation K ℝ≥0) : Prop where
  /-- `p` is a prime number. -/
  prime : p.Prime
  /-- `K` is complete for the topology defined by `v`. -/
  complete : CompleteSpace (WithVal v)
  /-- The valuation is nontrivial. -/
  nontrivial : ∃ x : K, v x ≠ 0 ∧ v x ≠ 1
  /-- The value group is dense (the valuation is non-discrete). -/
  nondiscrete : ∀ x : K, v x < 1 → ∃ y : K, v x < v y ∧ v y < 1
  /-- The residue characteristic is `p`. -/
  residue_char : v (p : K) < 1
  /-- Frobenius is surjective on `𝒪_K / p 𝒪_K`. -/
  frobenius_surjective :
    ∀ x : K, v x ≤ 1 → ∃ y : K, v y ≤ 1 ∧ v (y ^ p - x) ≤ v (p : K)

/-- In characteristic `p`, a perfectoid field is a perfect field: `x ↦ xᵖ` is a bijection. -/
