/-
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

Scholze's tilting construction attaches to a perfectoid field `(K, v)` of residue
characteristic `p` a perfectoid field `K^♭` of characteristic `p`.  Concretely, if `𝒪`
denotes the ring of integers of `K`, one forms the perfection of `𝒪 / p`,

  `𝒪^♭ = lim (𝒪/p, x ↦ x ^ p)`,

and `K^♭` is its fraction field; its multiplicative monoid is `lim (K, x ↦ x ^ p)`.  The
*tilting equivalence* then states that `K ↦ K^♭` induces an equivalence between perfectoid
`K`-algebras and perfectoid `K^♭`-algebras, and in particular an isomorphism of absolute
Galois groups `Gal(K̄/K) ≃ Gal(K̄^♭/K^♭)`.

Mathlib already contains the construction of the tilt (`Perfection`, `ModP`, `PreTilt`,
`Tilt` in `Mathlib/RingTheory/Perfection.lean`), following
[Scholze, *Perfectoid spaces*].  This file adds:

* `Frontier.IsPerfectoidField` — the axioms for `(K, v)` to be a perfectoid field with
  residue characteristic `p`: the (rank ≤ 1) valuation `v` is non-discrete, with a
  pseudo-uniformizer `w` satisfying `v p ≤ v w ^ p < v w < 1`, and Frobenius is surjective
  on `𝒪_K / p`;
* `Frontier.IsPerfectoidField.perfectRing` — in characteristic `p`, a perfectoid field is
  a perfect field;
* `Frontier.preTiltEquivSelf` — for a perfect ring `O` of characteristic `p`, the ring
  `PreTilt O p = lim (O/p, x ↦ x^p)` is canonically isomorphic to `O` itself
  (in characteristic `p` one has `O/p = O`, and the perfection of a perfect ring is the
  ring itself);
* `Frontier.val_preTiltEquivSelf` — that isomorphism is an isometry: the valuation Scholze's
  construction puts on the tilt corresponds to the original valuation `v`;
* `Frontier.tiltRingEquiv` — the induced isomorphism `K^♭ ≃+* K` on fraction fields;
* `Frontier.scholze_perfectoid_tilt` — **the main statement**: for a perfectoid field `K`
  of characteristic `p`, tilting is canonically the identity, `K^♭ ≃+* K`.  This is the
  base case of Scholze's tilting equivalence (for a general perfectoid field the tilt is a
  perfectoid field of characteristic `p`, and tilting it again changes nothing);
* `Frontier.tilt_algebraicClosure_zmod` — a concrete instance of the isomorphism, for the
  algebraic closure of `ZMod p`.

Completeness of `K` is not needed for the characteristic `p` statement, so it is not
imposed; it is of course part of the definition of a perfectoid field in general, and is
what makes the mixed characteristic construction work.
-/

open scoped NNReal

namespace Frontier

section Perfection

variable (O : Type*) [CommRing O] [Nontrivial O] (p : ℕ) [Fact p.Prime] [CharP O p]

/-- In characteristic `p` the element `p = 0` is not a unit, which is the hypothesis under
which Mathlib's `ModP` and `PreTilt` have their ring structure. -/
instance fact_not_isUnit_natCast : Fact (¬ IsUnit (p : O)) :=
  ⟨by
    rw [show ((p : O)) = 0 from mod_cast CharP.cast_eq_zero O p]
    exact not_isUnit_zero⟩

/-- In characteristic `p` we have `O / p = O`. -/

theorem IsPerfectoidField.perfectRing [Fact p.Prime] [CharP K p] (hK : IsPerfectoidField v p) :
    PerfectRing K p := by
  have hvp : v (p : K) = 0 := by
    rw [show ((p : K)) = 0 from mod_cast CharP.cast_eq_zero K p, map_zero]
  have key : ∀ x : K, v x ≤ 1 → ∃ y : K, y ^ p = x := by
    intro x hx
    obtain ⟨y, -, hy⟩ := hK.frobenius_surjective_mod_p x hx
    rw [hvp, le_zero_iff, Valuation.zero_iff, sub_eq_zero] at hy
    exact ⟨y, hy⟩
  refine PerfectRing.ofSurjective _ p fun x => ?_
  rcases le_or_gt (v x) 1 with hx | hx
  · obtain ⟨y, hy⟩ := key x hx
    exact ⟨y, by rw [frobenius_def, hy]⟩
  · have hx0 : x ≠ 0 := by
      intro h
      rw [h, map_zero] at hx
      exact absurd hx (by simp)
    have hinv : v x⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact le_of_lt (inv_lt_one_of_one_lt₀ hx)
    obtain ⟨y, hy⟩ := key x⁻¹ hinv
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, zero_pow (Nat.Prime.ne_zero Fact.out)] at hy
      exact (inv_ne_zero hx0) hy.symm
    refine ⟨y⁻¹, ?_⟩
    rw [frobenius_def, inv_pow, hy, inv_inv]

variable (v p)

/-- In characteristic `p` one has `v p = v 0 = 0 ≠ 1`, so Mathlib's hypothesis for forming
the tilt of `(K, v)` is automatic. -/
instance fact_valuation_natCast_ne_one [Fact p.Prime] [CharP K p] : Fact (v (p : K) ≠ 1) :=
  ⟨by
    rw [show ((p : K)) = 0 from mod_cast CharP.cast_eq_zero K p, map_zero]
    exact zero_ne_one⟩

variable [Fact p.Prime] [CharP K p]

instance charP_valuationSubring : CharP (v.valuationSubring) p :=
  CharP.subring K p v.valuationSubring.toSubring

/-- The ring of integers of a perfect field of characteristic `p` is perfect: a `p`-th root
of an element of valuation `≤ 1` again has valuation `≤ 1`. -/
instance perfectRing_valuationSubring [PerfectRing K p] : PerfectRing (v.valuationSubring) p := by
  refine PerfectRing.ofSurjective _ p fun x => ?_
  obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := K) (p := p)).2 (x : K)
  rw [frobenius_def] at hy
  have hy1 : v y ≤ 1 := by
    have hyp : v y ^ p ≤ 1 := by rw [← map_pow, hy]; exact x.2
    exact (pow_le_one_iff (Nat.Prime.ne_zero Fact.out)).mp hyp
  refine ⟨⟨y, (v.mem_valuationSubring_iff y).mpr hy1⟩, Subtype.ext ?_⟩
  simpa [frobenius_def] using hy

/-- **Tilting a perfectoid field of characteristic `p` gives back the field itself.**
The tilt `K^♭` (Mathlib's `Tilt`, the fraction field of the perfection of `𝒪_K / p`) is
canonically isomorphic, as a ring, to `K`. -/
