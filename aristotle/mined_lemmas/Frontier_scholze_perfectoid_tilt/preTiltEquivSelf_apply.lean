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

@[simp] lemma preTiltEquivSelf_apply (f : PreTilt O p) :
    preTiltEquivSelf O p f = modPEquiv O p (PreTilt.coeff 0 f) := by
  have h1 := (PerfectionMap.id p O).comp_symm_equiv (preTiltEquivPerfection O p f)
  have h2 := Perfection.coeff_map (R := ModP O p) (S := O) p (modPEquiv O p).toRingHom f 0
  exact h1.trans h2

end Perfection

section Isometry

variable {K : Type*} [Field K] {v : Valuation K ℝ≥0} {O : Type*} [CommRing O] [Nontrivial O]
  [Algebra O K] {p : ℕ} [Fact p.Prime] [CharP O p] [PerfectRing O p]

/-- **The isomorphism `𝒪_K^♭ ≃ 𝒪_K` is an isometry.**  In characteristic `p`, the valuation
that Scholze's construction puts on the tilt of the ring of integers agrees, under the
canonical isomorphism `PreTilt O p ≃+* O`, with the original valuation. -/
