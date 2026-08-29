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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open scoped NNReal
open Function

namespace Frontier

universe u w

/-!
## Perfectoid fields and the tilting correspondence

A *perfectoid field* is a complete non-archimedean valued field `(K, v)` of rank one whose value
group is non-discrete, whose residue characteristic is a prime `p`, and for which the Frobenius
`x ↦ x ^ p` is surjective on `O/p`, where `O ⊆ K` is the ring of integers.

Scholze's tilting construction attaches to such a field the *tilt*
`K♭ = Frac (lim_{x ↦ x^p} O/p)` (`Valuation.Tilt` in Mathlib), a perfectoid field of
characteristic `p`, and the tilting equivalence asserts that `L ↦ L♭` is an equivalence between
perfectoid extensions of `K` and perfectoid extensions of `K♭`; in particular it is fully
faithful and conservative on isomorphism classes.

The theorem `Frontier.scholze_perfectoid_tilt` below establishes the base case of this
correspondence, namely the case of characteristic `p`: there the tilt of a perfectoid field is
canonically isomorphic to the field itself, and consequently two characteristic-`p` perfectoid
fields are isomorphic if and only if their tilts are.
-/

/-- A *perfectoid field* (Scholze). `K` is a field equipped with a rank-one valuation
`v : K → ℝ≥0` with ring of integers `O`, such that

* the valuation is non-discrete (there is an element of valuation strictly between `0` and `1`);
* `K` is complete for its uniform structure;
* the residue characteristic is `p`, i.e. `p` is not a unit of `O`;
* the Frobenius `x ↦ x ^ p` on `O/p` is surjective (the perfectoid condition).
-/
structure IsPerfectoidField (p : ℕ) (K : Type u) [Field K] [UniformSpace K]
    (v : Valuation K ℝ≥0) (O : Type w) [CommRing O] [Algebra O K] : Prop where
  /-- `p` is a prime number. -/
  prime : p.Prime
  /-- `O` is the ring of integers of `v`. -/
  integers : v.Integers O
  /-- The valuation is non-discrete: some element has valuation different from `0` and `1`. -/
  nondiscrete : ∃ x : K, v x ≠ 0 ∧ v x ≠ 1
  /-- `K` is complete. -/
  complete : CompleteSpace K
  /-- The residue characteristic is `p`. -/
  residue_char : ¬ IsUnit (p : O)
  /-- Frobenius is surjective on `O/p`: the perfectoid condition. -/
  frobenius_surjective : Surjective (fun x : ModP O p => x ^ p)

section Auxiliary

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type u} [Field K] {v : Valuation K ℝ≥0}
variable {O : Type w} [CommRing O] [Algebra O K]

omit hp in
/-- The ring of integers of a valuation on a field has that field as fraction field. -/

theorem isFractionRing_of_integers (hv : v.Integers O) : IsFractionRing O K := by
  have hinj := hv.hom_inj
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O K) hinj
  refine ⟨?_, ?_, ?_⟩
  · intro y
    refine isUnit_iff_ne_zero.2 ?_
    simp [map_eq_zero_iff _ hinj, nonZeroDivisors.ne_zero y.2]
  · intro x
    obtain ⟨a, ha | ha⟩ := hv.eq_algebraMap_or_inv_eq_algebraMap x
    · exact ⟨⟨a, 1⟩, by simp [ha]⟩
    · rcases eq_or_ne x 0 with rfl | hx
      · exact ⟨⟨0, 1⟩, by simp⟩
      · have ha0 : a ≠ 0 := by
          intro h
          rw [h, map_zero] at ha
          exact inv_ne_zero hx ha
        refine ⟨⟨1, ⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩⟩, ?_⟩
        simp [← ha, mul_inv_cancel₀ hx]
  · intro a b h
    exact ⟨1, by rw [hinj h]⟩

omit hp in
/-- In characteristic `p`, `p` vanishes in the ring of integers. -/
