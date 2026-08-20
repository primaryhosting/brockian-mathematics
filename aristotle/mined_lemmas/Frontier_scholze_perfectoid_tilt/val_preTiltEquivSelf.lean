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

theorem val_preTiltEquivSelf (hv : v.Integers O) (f : PreTilt O p) :
    PreTilt.val K v O hv p f = v (algebraMap O K (preTiltEquivSelf O p f)) := by
  by_cases hf : f = 0
  · subst hf; simp
  · have hc : PreTilt.coeff 0 f ≠ 0 := by
      intro h
      refine hf ((preTiltEquivSelf O p).injective ?_)
      rw [preTiltEquivSelf_apply, h, map_zero, map_zero]
    have hval : PreTilt.val K v O hv p f = ModP.preVal K v O p (PreTilt.coeff 0 f) := by
      simpa using PreTilt.valAux_eq (v := v) hv (f := f) (n := 0) hc
    have hmk : Ideal.Quotient.mk (Ideal.span {(p : O)}) (modPEquiv O p (PreTilt.coeff 0 f)) ≠ 0 := by
      rw [mk_modPEquiv]; exact hc
    have key := ModP.preVal_mk hv (p := p) (x := modPEquiv O p (PreTilt.coeff 0 f)) hmk
    rw [mk_modPEquiv] at key
    rw [hval, preTiltEquivSelf_apply, key]

end Isometry

section PerfectoidField

variable {K : Type*} [Field K] (v : Valuation K ℝ≥0) (p : ℕ)

/-- The axioms for `(K, v)` to be a perfectoid field with residue characteristic `p`:
the (rank ≤ 1) valuation `v` is non-discrete, in the strong sense that there is a
*pseudo-uniformizer* `w` with `v p ≤ v w ^ p < v w < 1`, and the Frobenius `x ↦ x ^ p` is
surjective on `𝒪_K / p`.  (Completeness of `K` for the `v`-adic topology is part of the
usual definition; it is not needed for any statement in this file, so it is imposed
separately where relevant.) -/
structure IsPerfectoidField : Prop where
  /-- `v` is non-discrete: there is a pseudo-uniformizer. -/
  exists_pseudoUniformizer : ∃ w : K, v (p : K) ≤ v w ^ p ∧ v w ^ p < v w ∧ v w < 1
  /-- Frobenius is surjective on `𝒪_K / p`. -/
  frobenius_surjective_mod_p :
    ∀ x : K, v x ≤ 1 → ∃ y : K, v y ≤ 1 ∧ v (y ^ p - x) ≤ v (p : K)

variable {v p}

/-- A perfectoid field of characteristic `p` is a perfect field: modulo `p = 0`, the
Frobenius-surjectivity axiom says that every element of `𝒪_K` is a `p`-th power, and
inverting gives all of `K`. -/
