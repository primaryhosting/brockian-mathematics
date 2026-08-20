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

theorem scholze_perfectoid_tilt
    {p : ℕ} [Fact p.Prime] {K : Type*} {Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CharP K p]
    (hK : IsPerfectoidField p K Γ₀) :
    -- the tilt of any characteristic-`p` ring is a perfect ring of characteristic `p`
    (∀ (R : Type) (_ : CommRing R) (_ : CharP R p),
        CharP (Tilt p R) p ∧ Function.Bijective (frobenius (Tilt p R) p)) ∧
    -- Frobenius is bijective on a characteristic-`p` perfectoid field
    Function.Bijective (frobenius K p) ∧
    -- and tilting is (canonically) the identity on such a field
    ∃ e : K ≃+* Tilt p K, ∀ x : K, Tilt.sharp (e x) = x := by
  refine ⟨?_, ?_, ?_⟩
  · intro R _ _
    exact ⟨Tilt.charP, tilt_frobenius_bijective⟩
  · exact frobenius_bijective_of_perfectoid_charP hK
  · exact ⟨tiltEquivOfPerfect (frobenius_bijective_of_perfectoid_charP hK), fun x => rfl⟩


/-! ## The tilt in mixed characteristic

For a perfectoid field `K` of any characteristic, the ring of integers of the tilt `K♭` is
constructed as the inverse limit of Frobenius on `𝒪_K / p 𝒪_K`.  We check here that this ring
is well defined and is a perfect ring of characteristic `p`.
-/

section MixedChar

/-- A nontrivial commutative ring in which a prime `p` vanishes has characteristic `p`. -/
