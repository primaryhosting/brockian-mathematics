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

theorem isPerfectoidField_of_perfect [CompleteSpace K]
    (hperf : Function.Bijective (frobenius K p))
    (hnt : ∃ x : K, Valued.v x ≠ (0 : Γ₀) ∧ Valued.v x ≠ 1)
    (hnd : ∀ x : K, Valued.v x ≠ (0 : Γ₀) → Valued.v x < 1 →
      ∃ y : K, Valued.v x < Valued.v y ∧ Valued.v y < (1 : Γ₀)) :
    IsPerfectoidField p K Γ₀ where
  prime := Fact.out
  complete := ‹CompleteSpace K›
  nontrivial := hnt
  nondiscrete := hnd
  residue_char := by rw [CharP.cast_eq_zero K p, map_zero]; exact zero_lt_one
  frobenius_surjective := by
    intro x hx
    have hpow : Valued.v (pRoot hperf x) ^ p = (Valued.v x : Γ₀) := by rw [← map_pow, pRoot_pow]
    have hy : Valued.v (pRoot hperf x) ≤ (1 : Γ₀) := by
      by_contra hc
      push_neg at hc
      have h1 : 1 < Valued.v (pRoot hperf x) ^ p :=
        one_lt_pow₀ hc (Nat.Prime.pos (Fact.out (p := p.Prime))).ne'
      rw [hpow] at h1
      exact absurd hx (not_le.2 h1)
    exact ⟨pRoot hperf x, 0, hy, by simp, by simp [pRoot_pow]⟩

end PerfectoidCharP

/-! ## The tilting theorem (base case) -/

/--
**Scholze's tilting for perfectoid fields — formalized statement and characteristic `p` base
case.**

For any commutative ring `R` of characteristic `p`, the tilt `R♭ = lim_{x ↦ x^p} R` is a ring of
characteristic `p` on which Frobenius is bijective (a perfect ring); this is the general
construction underlying Scholze's tilting equivalence.

For a perfectoid field `K` of characteristic `p` (the base case of the tilting equivalence,
where the tilting functor is the identity), the canonical map `K → K♭` is a ring isomorphism
inverted by the sharp map `♯ : K♭ → K`; in particular `K ≅ K♭` as fields.
-/
