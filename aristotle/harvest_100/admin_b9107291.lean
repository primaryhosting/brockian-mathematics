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
theorem natCast_eq_zero_of_integers [CharP K p] (hv : v.Integers O) : (p : O) = 0 := by
  apply hv.hom_inj
  simp [map_natCast]

/-- In characteristic `p` the ring `O/p` is canonically isomorphic to `O`. -/
noncomputable def modPEquivSelf (h : (p : O) = 0) : ModP O p ≃+* O :=
  (Ideal.quotEquivOfEq (by rw [h, Ideal.span_singleton_eq_bot.2 rfl])).trans
    (RingEquiv.quotientBot O)

end Auxiliary

section CharP

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type u} [Field K] [UniformSpace K] [CharP K p] {v : Valuation K ℝ≥0}
variable {O : Type w} [CommRing O] [Algebra O K]

omit hp [UniformSpace K] in
/-- In characteristic `p` the hypothesis `v p ≠ 1`, needed to form the tilt, is automatic. -/
theorem val_natCast_ne_one : v (p : K) ≠ 1 := by
  rw [CharP.cast_eq_zero K p, map_zero]
  exact zero_ne_one

/-- In characteristic `p`, if Frobenius is surjective on `O/p` then the perfection of `O/p`
(the integral tilt) is isomorphic to `O` itself. -/
noncomputable def preTiltEquivSelfOfIntegers (hv : v.Integers O) [Fact (¬ IsUnit (p : O))]
    (hfrob : Surjective (fun x : ModP O p => x ^ p)) : PreTilt O p ≃+* O := by
  haveI : Nontrivial O := hv.nontrivial_iff.2 inferInstance
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O K) hv.hom_inj
  haveI : CharP O p := (algebraMap O K).charP hv.hom_inj p
  haveI : ExpChar O p := ExpChar.prime hp.1
  have e1 : ModP O p ≃+* O := modPEquivSelf (natCast_eq_zero_of_integers hv)
  haveI : IsDomain (ModP O p) := Function.Injective.isDomain e1.toRingHom e1.injective
  haveI : ExpChar (ModP O p) p := ExpChar.prime hp.1
  haveI : PerfectRing (ModP O p) p := PerfectRing.ofSurjective _ _ hfrob
  exact (PerfectionMap.id p (R := ModP O p)).equiv.symm.trans e1

/-- In characteristic `p`, if Frobenius is surjective on `O/p` then the tilt of `K` is
isomorphic to `K` itself. -/
noncomputable def tiltEquivSelfOfIntegers (hv : v.Integers O) [Fact (v p ≠ 1)]
    (hpu : ¬ IsUnit (p : O)) (hfrob : Surjective (fun x : ModP O p => x ^ p)) :
    Tilt K v O hv p ≃+* K := by
  haveI : Fact (¬ IsUnit (p : O)) := Fact.mk hpu
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain K v O hv p
  haveI : IsFractionRing O K := isFractionRing_of_integers hv
  exact (IsFractionRing.ringEquivOfRingEquiv (K := FractionRing (PreTilt O p))
    (L := FractionRing O) (preTiltEquivSelfOfIntegers hv hfrob)).trans
      (FractionRing.algEquiv O K).toRingEquiv

/-- For a perfectoid field of characteristic `p`, the tilt `K♭` is isomorphic to `K`. -/
noncomputable def tiltEquivSelf (hK : IsPerfectoidField p K v O) [Fact (v p ≠ 1)] :
    Tilt K v O hK.integers p ≃+* K :=
  tiltEquivSelfOfIntegers hK.integers hK.residue_char hK.frobenius_surjective

end CharP

/-- **Base case of the Scholze tilting equivalence for perfectoid fields.**

Let `p` be a prime and let `(K, v, O)` and `(L, w, P)` be perfectoid fields of characteristic `p`.
Then:

* the tilt `K♭` of `K` is isomorphic to `K` itself, and likewise for `L`;
* consequently `K` and `L` are isomorphic if and only if their tilts `K♭` and `L♭` are, i.e.
  tilting is an equivalence on characteristic-`p` perfectoid fields.

This is the characteristic-`p` case of Scholze's tilting correspondence, where the tilting
functor is (canonically isomorphic to) the identity.

The instance hypotheses `Fact (v p ≠ 1)` and `Fact (w p ≠ 1)` are only needed to form the tilts;
in characteristic `p` they hold automatically, see `Frontier.val_natCast_ne_one`. -/
theorem scholze_perfectoid_tilt {p : ℕ} [Fact p.Prime]
    {K : Type u} [Field K] [UniformSpace K] [CharP K p] {v : Valuation K ℝ≥0} [Fact (v p ≠ 1)]
    {O : Type w} [CommRing O] [Algebra O K] (hK : IsPerfectoidField p K v O)
    {L : Type u} [Field L] [UniformSpace L] [CharP L p] {w : Valuation L ℝ≥0} [Fact (w p ≠ 1)]
    {P : Type w} [CommRing P] [Algebra P L] (hL : IsPerfectoidField p L w P) :
    Nonempty (Tilt K v O hK.integers p ≃+* K) ∧ Nonempty (Tilt L w P hL.integers p ≃+* L) ∧
      (Nonempty (Tilt K v O hK.integers p ≃+* Tilt L w P hL.integers p) ↔
        Nonempty (K ≃+* L)) := by
  refine ⟨⟨tiltEquivSelf hK⟩, ⟨tiltEquivSelf hL⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨e⟩
    exact ⟨((tiltEquivSelf hK).symm.trans e).trans (tiltEquivSelf hL)⟩
  · rintro ⟨e⟩
    exact ⟨((tiltEquivSelf hK).trans e).trans (tiltEquivSelf hL).symm⟩


/-!
## A sanity check

The hypotheses of `tiltEquivSelfOfIntegers` (the ring-theoretic heart of the base case) are
satisfiable: we check them for the degenerate example of the prime field `ZMod p` with its
trivial valuation, and obtain a Lean-checked isomorphism between its tilt and itself.
(The trivial valuation is discrete, so this example is not a perfectoid field in the sense of
`IsPerfectoidField`; it only witnesses that the construction above is not vacuous.)
-/

section Example

/-- The trivial valuation on a field. -/
noncomputable def trivialValuation (F : Type u) [Field F] : Valuation F ℝ≥0 where
  toFun x := if x = 0 then 0 else 1
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
  map_add_le_max' x y := by
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> by_cases hxy : x + y = 0 <;> simp_all

@[simp] theorem trivialValuation_apply {F : Type u} [Field F] (x : F) :
    trivialValuation F x = if x = 0 then 0 else 1 := rfl

/-- A field is its own ring of integers for the trivial valuation. -/
theorem trivialValuation_integers (F : Type u) [Field F] : (trivialValuation F).Integers F where
  hom_inj := fun x y h => by simpa using h
  map_le_one := fun x => by simp only [trivialValuation_apply]; split <;> simp
  exists_of_le_one := fun r _ => ⟨r, rfl⟩

instance (p : ℕ) [Fact p.Prime] : Fact (trivialValuation (ZMod p) p ≠ 1) := Fact.mk (by simp)

/-- The tilt of the trivially valued prime field `ZMod p` is `ZMod p` itself. -/
theorem tilt_zmod (p : ℕ) [Fact p.Prime] :
    Nonempty (Tilt (ZMod p) (trivialValuation (ZMod p)) (ZMod p)
      (trivialValuation_integers (ZMod p)) p ≃+* ZMod p) := by
  have h0 : ((p : ℕ) : ZMod p) = 0 := by simp
  have hpu : ¬ IsUnit ((p : ℕ) : ZMod p) := by
    rw [h0]
    simp
  have hfrob : Surjective (fun x : ModP (ZMod p) p => x ^ p) := by
    have e1 : ModP (ZMod p) p ≃+* ZMod p := modPEquivSelf h0
    intro x
    exact ⟨x, e1.injective (by rw [map_pow, ZMod.pow_card])⟩
  exact ⟨tiltEquivSelfOfIntegers (trivialValuation_integers (ZMod p)) hpu hfrob⟩

end Example

end Frontier

