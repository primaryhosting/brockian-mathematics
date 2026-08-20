/-
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The tilt: inverse limit along Frobenius -/

section Tilt

variable (p : ℕ) (R : Type*) [CommRing R] [Fact p.Prime] [CharP R p]

/-- The **tilt** of a commutative ring `R` of characteristic `p`: the inverse limit
`lim_{x ↦ x^p} R`, realised as the subring of sequences `f : ℕ → R` satisfying
`f (n+1) ^ p = f n`. -/

@[simp] lemma sharp_tiltEquivOfPerfect (x : R) :
    Tilt.sharp (tiltEquivOfPerfect hperf x) = x := rfl

end CharPCase

/-! ## Perfectoid fields -/

/-- A **perfectoid field**: a field `K`, complete with respect to a rank-one nonarchimedean
valuation `v` which is nontrivial and non-discrete, of residue characteristic `p`, and such that
the Frobenius `x ↦ x^p` is surjective on `𝒪_K / p 𝒪_K`. -/
structure IsPerfectoidField (p : ℕ) (K : Type*) (Γ₀ : Type*) [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] : Prop where
  /-- `p` is a prime number. -/
  prime : p.Prime
  /-- `K` is complete for the valuation topology. -/
  complete : CompleteSpace K
  /-- The valuation is nontrivial. -/
  nontrivial : ∃ x : K, Valued.v x ≠ (0 : Γ₀) ∧ Valued.v x ≠ 1
  /-- The value group is non-discrete: values accumulate at `1` from below. -/
  nondiscrete : ∀ x : K, Valued.v x ≠ (0 : Γ₀) → Valued.v x < 1 →
    ∃ y : K, Valued.v x < Valued.v y ∧ Valued.v y < (1 : Γ₀)
  /-- The residue characteristic is `p`. -/
  residue_char : Valued.v (p : K) < (1 : Γ₀)
  /-- Frobenius is surjective on `𝒪_K / p 𝒪_K`. -/
  frobenius_surjective :
    ∀ x : K, Valued.v x ≤ (1 : Γ₀) →
      ∃ y z : K, Valued.v y ≤ (1 : Γ₀) ∧ Valued.v z ≤ (1 : Γ₀) ∧ x - y ^ p = (p : K) * z

section PerfectoidCharP

variable {p : ℕ} {K : Type*} {Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  [Valued K Γ₀] [Fact p.Prime] [CharP K p]

/-- **A perfectoid field of characteristic `p` is perfect.** -/
