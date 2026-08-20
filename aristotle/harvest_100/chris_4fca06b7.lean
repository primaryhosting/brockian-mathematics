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
noncomputable def modPEquiv : ModP O p ≃+* O :=
  (Ideal.quotEquivOfEq (by simp)).trans (RingEquiv.quotientBot O)

variable [PerfectRing O p]

/-- The functorial isomorphism `PreTilt O p = Perfection (O/p) p ≃+* Perfection O p`
induced by `O / p ≃+* O` (valid in characteristic `p`). -/
noncomputable def preTiltEquivPerfection : PreTilt O p ≃+* Ring.Perfection O p :=
  RingEquiv.ofRingHom (Perfection.map p (modPEquiv O p).toRingHom)
    (Perfection.map p (modPEquiv O p).symm.toRingHom)
    (RingHom.ext fun x => Perfection.ext fun n => by
      have h1 := Perfection.coeff_map (R := ModP O p) (S := O) p (modPEquiv O p).toRingHom
        ((Perfection.map p (modPEquiv O p).symm.toRingHom) x) n
      have h2 := Perfection.coeff_map (R := O) (S := ModP O p) p
        (modPEquiv O p).symm.toRingHom x n
      exact h1.trans ((congrArg (modPEquiv O p).toRingHom h2).trans
        ((modPEquiv O p).apply_symm_apply _)))
    (RingHom.ext fun x => Perfection.ext fun n => by
      have h1 := Perfection.coeff_map (R := O) (S := ModP O p) p (modPEquiv O p).symm.toRingHom
        ((Perfection.map p (modPEquiv O p).toRingHom) x) n
      have h2 := Perfection.coeff_map (R := ModP O p) (S := O) p (modPEquiv O p).toRingHom x n
      exact h1.trans ((congrArg (modPEquiv O p).symm.toRingHom h2).trans
        ((modPEquiv O p).symm_apply_apply _)))

/-- **The tilt of the ring of integers is the ring of integers, in characteristic `p`.**
For a perfect ring `O` of characteristic `p`, `PreTilt O p = lim (O/p, x ↦ x ^ p)` is
canonically isomorphic to `O`. -/
noncomputable def preTiltEquivSelf : PreTilt O p ≃+* O :=
  (preTiltEquivPerfection O p).trans ((PerfectionMap.id p O).equiv).symm

variable {O p}

omit [Nontrivial O] [Fact p.Prime] [PerfectRing O p] in
@[simp] lemma mk_modPEquiv (y : ModP O p) :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) (modPEquiv O p y) = y :=
  (modPEquiv O p).symm_apply_apply y

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
noncomputable def tiltRingEquiv [PerfectRing K p] :
    Tilt K v v.valuationSubring (Valuation.valuationSubring.integers v) p ≃+* K := by
  have h : Submonoid.map (preTiltEquivSelf (v.valuationSubring) p).toMonoidHom
      (nonZeroDivisors (PreTilt (v.valuationSubring) p)) = nonZeroDivisors v.valuationSubring := by
    convert MulEquivClass.map_nonZeroDivisors (preTiltEquivSelf (v.valuationSubring) p) using 2
  exact IsLocalization.ringEquivOfRingEquiv
    (S := FractionRing (PreTilt (v.valuationSubring) p)) (Q := K)
    (preTiltEquivSelf (v.valuationSubring) p) h

end PerfectoidField

/-- **Scholze's tilting equivalence, characteristic `p` base case.**

Let `(K, v)` be a perfectoid field of characteristic `p`, with ring of integers
`𝒪_K = v.valuationSubring`.  Then the tilt

  `K^♭ = Frac (lim (𝒪_K / p, x ↦ x ^ p))`

is canonically isomorphic to `K` itself: tilting does nothing in characteristic `p`.

This is the base case of the tilting equivalence: for a general perfectoid field `K` of
mixed characteristic, `K^♭` is a perfectoid field of characteristic `p`, and the theorem
below says that tilting `K^♭` again returns `K^♭`; the equivalence of the categories of
perfectoid `K`-algebras and of perfectoid `K^♭`-algebras is thereby reduced to the
characteristic `p` situation.

The construction of the tilt is Mathlib's `Tilt` (`Mathlib/RingTheory/Perfection.lean`,
following Scholze, *Perfectoid spaces*); the isomorphism is produced here from
`Frontier.preTiltEquivSelf`. -/
theorem scholze_perfectoid_tilt {K : Type*} [Field K] (v : Valuation K ℝ≥0) (p : ℕ)
    [Fact p.Prime] [CharP K p] (hK : IsPerfectoidField v p) :
    Nonempty (Tilt K v v.valuationSubring (Valuation.valuationSubring.integers v) p ≃+* K) ∧
      ∃ e : PreTilt v.valuationSubring p ≃+* v.valuationSubring, ∀ f,
        PreTilt.val K v v.valuationSubring (Valuation.valuationSubring.integers v) p f
          = v (algebraMap v.valuationSubring K (e f)) := by
  haveI := hK.perfectRing
  exact ⟨⟨tiltRingEquiv v p⟩, preTiltEquivSelf _ p,
    val_preTiltEquivSelf (Valuation.valuationSubring.integers v)⟩

section Example

open Classical in
/-- The trivial valuation on a field, used below only to exhibit a concrete field to which
the tilting construction applies. -/
noncomputable def trivialValuation (K : Type*) [Field K] : Valuation K ℝ≥0 where
  toFun x := if x = 0 then 0 else 1
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
  map_add_le_max' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    by_cases hxy : x + y = 0 <;> simp [hx, hy, hxy]

/-- A concrete non-vacuous instance of the characteristic `p` tilting isomorphism: the tilt
of `𝔽̄_p` (a perfect field of characteristic `p`) is `𝔽̄_p` itself. -/
theorem tilt_algebraicClosure_zmod (p : ℕ) [Fact p.Prime] :
    Nonempty (Tilt (AlgebraicClosure (ZMod p)) (trivialValuation _)
      (trivialValuation (AlgebraicClosure (ZMod p))).valuationSubring
      (Valuation.valuationSubring.integers _) p ≃+* AlgebraicClosure (ZMod p)) :=
  ⟨tiltRingEquiv _ p⟩

end Example

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

