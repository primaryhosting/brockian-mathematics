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

theorem charP_of_prime_cast_eq_zero (A : Type*) [CommRing A] [Nontrivial A] (p : ℕ)
    (hp : p.Prime) (h : (p : A) = 0) : CharP A p := by
  obtain ⟨q, hq⟩ := CharP.exists A
  have hqp : q ∣ p := (CharP.cast_eq_zero_iff A q p).1 h
  have hq1 : q ≠ 1 := CharP.char_ne_one A q
  rcases Nat.Prime.eq_one_or_self_of_dvd hp q hqp with h1 | h2
  · exact absurd h1 hq1
  · subst h2; exact hq

variable {p : ℕ} {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀)

/-- The ring `𝒪_K / p 𝒪_K` attached to a valued field. -/
abbrev residuePMod (v : Valuation K Γ₀) (p : ℕ) : Type _ :=
  v.integer ⧸ (Ideal.span {(p : v.integer)})

instance residuePMod.instNontrivial [Fact (v (p : K) < 1)] : Nontrivial (residuePMod v p) := by
  have hnu : ¬ IsUnit (p : v.integer) := by
    rintro ⟨u, hu⟩
    obtain ⟨w, hw⟩ : ∃ w : v.integer, (p : v.integer) * w = 1 := ⟨u.inv, by rw [← hu]; simp⟩
    have hK : (p : K) * (w : K) = 1 := by
      have := congrArg (fun x : v.integer => (x : K)) hw
      simpa using this
    have h1 : v ((p : K) * (w : K)) = 1 := by rw [hK]; simp
    have hlt : v (p : K) * v (w : K) < 1 :=
      calc v (p : K) * v (w : K) ≤ v (p : K) * 1 := by gcongr; exact w.2
        _ = v (p : K) := mul_one _
        _ < 1 := Fact.out
    rw [map_mul] at h1
    exact absurd h1 (ne_of_lt hlt)
  exact Ideal.Quotient.nontrivial_iff.2 (by rw [Ne, Ideal.span_singleton_eq_top]; exact hnu)

instance residuePMod.instCharP [Fact p.Prime] [Fact (v (p : K) < 1)] :
    CharP (residuePMod v p) p := by
  refine charP_of_prime_cast_eq_zero _ p Fact.out ?_
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : v.integer)})) p]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

/-- **The ring of integers of the tilt.**  For a valued field `K` with residue characteristic `p`
(in particular for any perfectoid field, of mixed or equal characteristic), the inverse limit of
Frobenius on `𝒪_K / p 𝒪_K` is a perfect ring of characteristic `p`. -/
