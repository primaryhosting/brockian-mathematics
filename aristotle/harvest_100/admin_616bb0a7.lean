/-
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any doc-comment command, so the header above is
-- written as a plain block comment; the same text is repeated as a module docstring below.)

import Mathlib

/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

Let `K` be a field with a valuation `v : K → ℝ≥0` whose ring of integers is `O`
(`hv : v.Integers O`), and let `p` be a prime with `v p ≠ 1`.  Mathlib implements Scholze's
tilt `K♭` as `Tilt K v O hv p`, the fraction field of the perfection of `O/p`
(`Mathlib.RingTheory.Perfection`, following [scholze2011perfectoid]).

We prove:

* `Frontier.charP_tilt` : the tilt has characteristic `p`;
* `Frontier.tilt_pow_bijective` : the tilt is perfect, i.e. its Frobenius `x ↦ x ^ p` is
  bijective — so `K♭` is a perfect field of characteristic `p`;
* `Frontier.tilt_ringEquiv_self` : the base case of the tilting correspondence — if `K` is
  already a perfect field of characteristic `p`, then tilting is the identity: `K♭ ≃+* K`;
* `Frontier.scholze_perfectoid_tilt` : the three statements packaged together.

Along the way we prove some results of independent interest:
`Frontier.isFractionRing_integers` (a valued field is the fraction field of its ring of
integers), `Frontier.isFractionRing_of_div_surjective` and
`Frontier.isFractionRing_of_ringEquiv`.
-/

open scoped NNReal

namespace Frontier

/-! ### Generic helper lemmas -/

/-- If `A` is a domain sitting inside a field `F` such that every element of `F` is a quotient
of elements of `A`, then `F` is the fraction field of `A`. -/
theorem isFractionRing_of_div_surjective {A F : Type*} [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] (hinj : Function.Injective (algebraMap A F))
    (hdiv : ∀ z : F, ∃ a b : A, b ≠ 0 ∧ z = algebraMap A F a / algebraMap A F b) :
    IsFractionRing A F := by
  refine (isLocalization_iff (nonZeroDivisors A) F).mpr ⟨fun y => ?_, fun z => ?_,
    fun {x y} h => ⟨1, by rw [hinj h]⟩⟩
  · have hy : (y : A) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.2
    have : algebraMap A F y ≠ 0 := fun h => hy (hinj (by simpa using h))
    exact isUnit_iff_ne_zero.mpr this
  · obtain ⟨a, b, hb, rfl⟩ := hdiv z
    have hb' : algebraMap A F b ≠ 0 := fun h => hb (hinj (by simpa using h))
    exact ⟨⟨a, ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩⟩, by field_simp⟩

/-- Being a fraction field transfers along a ring isomorphism of the base. -/
theorem isFractionRing_of_ringEquiv {A B F : Type*} [CommRing A] [CommRing B] [IsDomain A]
    [IsDomain B] [Field F] [Algebra A F] [IsFractionRing A F] [Algebra B F] (e : B ≃+* A)
    (halg : ∀ x : B, algebraMap B F x = algebraMap A F (e x)) : IsFractionRing B F := by
  refine isFractionRing_of_div_surjective ?_ ?_
  · intro x y hxy
    rw [halg, halg] at hxy
    exact e.injective (IsFractionRing.injective A F hxy)
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    refine ⟨e.symm a, e.symm b, fun h => hb0 (by simpa using congrArg e h), ?_⟩
    rw [halg, halg]
    simp

/-- Surjectivity of the `p`-th power map transfers along a ring isomorphism. -/
theorem pow_surjective_of_ringEquiv {A B : Type*} (p : ℕ) [CommRing A] [CommRing B]
    (e : A ≃+* B) (h : Function.Surjective fun a : A => a ^ p) :
    Function.Surjective fun b : B => b ^ p := by
  intro b
  obtain ⟨a, ha⟩ := h (e.symm b)
  exact ⟨e a, by simpa using congrArg e ha⟩

/-- In a field of characteristic `p`, the `p`-th power map is injective. -/
theorem pow_injective_of_charP {F : Type*} [Field F] (p : ℕ) (hp : p.Prime) [CharP F p] :
    Function.Injective fun x : F => x ^ p := by
  haveI : ExpChar F p := .prime hp
  intro x y h
  simpa [frobenius_def] using frobenius_inj F p (by simpa [frobenius_def] using h)

/-- If every element of a domain `A` is a `p`-th power, then the same holds in its
fraction field. -/
theorem pow_surjective_fractionRing {A F : Type*} (p : ℕ) [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] (h : Function.Surjective fun a : A => a ^ p) :
    Function.Surjective fun x : F => x ^ p := by
  intro z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
  obtain ⟨c, hc⟩ := h a
  obtain ⟨d, hd⟩ := h b
  refine ⟨algebraMap A F c / algebraMap A F d, ?_⟩
  simp only at hc hd ⊢
  rw [div_pow, ← map_pow, ← map_pow, hc, hd]

/-- A field with a valuation is the fraction field of its ring of integers. -/
theorem isFractionRing_integers {K : Type*} [Field K] {v : Valuation K ℝ≥0}
    {O : Type*} [CommRing O] [Algebra O K] (hv : v.Integers O) : IsFractionRing O K := by
  haveI : Nontrivial O := hv.nontrivial_iff.mpr inferInstance
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O K) hv.hom_inj
  refine isFractionRing_of_div_surjective hv.hom_inj (fun z => ?_)
  by_cases hz : v z ≤ 1
  · obtain ⟨a, ha⟩ := hv.exists_of_le_one hz
    exact ⟨a, 1, one_ne_zero, by simp [ha]⟩
  · push_neg at hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have hvz : v z ≠ 0 := (Valuation.ne_zero_iff v).mpr hz0
    have h1 : v z⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact le_of_lt ((inv_lt_one₀ (by positivity)).mpr hz)
    obtain ⟨b, hb⟩ := hv.exists_of_le_one h1
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      exact hz0 (by simpa using (inv_eq_zero.mp hb.symm))
    exact ⟨1, b, hb0, by rw [hb]; simp⟩

/-! ### The tilt of a perfectoid field

`K` is a field equipped with a valuation `v : K → ℝ≥0` whose ring of integers is `O`
(`hv : v.Integers O`), and `p` is a prime with `v p ≠ 1`.  `Tilt K v O hv p` is Mathlib's
implementation of Scholze's tilt `K♭`: the fraction field of the perfection of `O/p`. -/

variable {K : Type*} [Field K] (v : Valuation K ℝ≥0)
  {O : Type*} [CommRing O] [Algebra O K] (hv : v.Integers O) (p : ℕ)
  [Fact p.Prime] [hvp : Fact (v p ≠ 1)]

/-- The tilt `K♭` of a valued field has characteristic `p`. -/
theorem charP_tilt : CharP (Tilt K v O hv p) p := by
  haveI := Fact.mk <| mt hv.one_of_isUnit <| (map_natCast (algebraMap O K) p).symm ▸ hvp.1
  haveI := PreTilt.isDomain K v O hv p
  show CharP (FractionRing (PreTilt O p)) p
  exact IsFractionRing.charP_of_isFractionRing (PreTilt O p) p

/-- The tilt `K♭` is a perfect field: the `p`-th power (Frobenius) map is bijective on it. -/
theorem tilt_pow_bijective : Function.Bijective fun x : Tilt K v O hv p => x ^ p := by
  haveI := Fact.mk <| mt hv.one_of_isUnit <| (map_natCast (algebraMap O K) p).symm ▸ hvp.1
  haveI := PreTilt.isDomain K v O hv p
  haveI := charP_tilt v hv p
  have hp : p.Prime := Fact.out
  refine ⟨pow_injective_of_charP (F := Tilt K v O hv p) p hp, ?_⟩
  have hsurj : Function.Surjective fun a : PreTilt O p => a ^ p := by
    intro a
    obtain ⟨b, hb⟩ := (PerfectRing.bijective_frobenius (R := PreTilt O p) (p := p)).2 a
    exact ⟨b, by simpa [frobenius_def] using hb⟩
  show Function.Surjective fun x : FractionRing (PreTilt O p) => x ^ p
  exact pow_surjective_fractionRing (A := PreTilt O p) p hsurj

/-- Base case of the tilting correspondence: if `K` is already a perfect field of
characteristic `p`, then tilting does nothing, i.e. `K♭ ≃+* K`.

Indeed in that case `p = 0` in `O`, so `O/p = O`; moreover `O` is perfect, hence equal to its
own perfection, and `K` is the fraction field of `O`. -/
theorem tilt_ringEquiv_self (hK : CharP K p) (hperf : Function.Surjective fun x : K => x ^ p) :
    Nonempty (Tilt K v O hv p ≃+* K) := by
  have hp : p.Prime := Fact.out
  haveI : Nontrivial O := hv.nontrivial_iff.mpr inferInstance
  haveI hdomO : IsDomain O := Function.Injective.isDomain (algebraMap O K) hv.hom_inj
  haveI hcharO : CharP O p := by
    constructor
    intro x
    rw [← hK.cast_eq_zero_iff x, ← map_natCast (algebraMap O K) x]
    exact ⟨fun h => by rw [h]; simp, fun h => hv.hom_inj (by simpa using h)⟩
  -- `p = 0` in `O`, hence `O/p = O`
  have hspan : Ideal.span {(p : O)} = ⊥ := by rw [CharP.cast_eq_zero O p]; simp
  have eq0 : ModP O p ≃+* O := (Ideal.quotEquivOfEq hspan).trans (RingEquiv.quotientBot O)
  -- `O` is perfect, since `K` is
  have hOsurj : Function.Surjective fun a : O => a ^ p := by
    intro x
    obtain ⟨y, hy⟩ := hperf (algebraMap O K x)
    simp only at hy
    have hvy : v y ≤ 1 := by
      by_contra hc
      push_neg at hc
      have h1 : (1 : ℝ≥0) < v y ^ p := by
        calc (1 : ℝ≥0) = 1 ^ p := (one_pow p).symm
        _ < v y ^ p := pow_lt_pow_left₀ hc (zero_le _) hp.ne_zero
      rw [← map_pow, hy] at h1
      exact absurd (hv.map_le_one x) (not_le.mpr h1)
    obtain ⟨o, ho⟩ := hv.exists_of_le_one hvy
    exact ⟨o, hv.hom_inj (by simp only [map_pow, ho, hy])⟩
  haveI : Fact (¬ IsUnit (p : O)) :=
    Fact.mk <| mt hv.one_of_isUnit <| (map_natCast (algebraMap O K) p).symm ▸ hvp.1
  haveI hdomModP : IsDomain (ModP O p) :=
    Function.Injective.isDomain (eq0 : ModP O p ≃+* O).toRingHom eq0.injective
  haveI : ExpChar (ModP O p) p := .prime hp
  haveI hperfModP : PerfectRing (ModP O p) p := by
    refine PerfectRing.ofSurjective _ p ?_
    intro x
    obtain ⟨y, hy⟩ := pow_surjective_of_ringEquiv p eq0.symm hOsurj x
    exact ⟨y, by simpa [frobenius_def] using hy⟩
  -- a perfect ring is its own perfection, so `PreTilt O p ≃+* O`
  have eqPerf : ModP O p ≃+* Ring.Perfection (ModP O p) p := (PerfectionMap.id p (ModP O p)).equiv
  have e1 : PreTilt O p ≃+* O := (show PreTilt O p ≃+* ModP O p from eqPerf.symm).trans eq0
  haveI hdomPre : IsDomain (PreTilt O p) := PreTilt.isDomain K v O hv p
  haveI : IsFractionRing O K := isFractionRing_integers hv
  letI : Algebra (PreTilt O p) K := ((algebraMap O K).comp e1.toRingHom).toAlgebra
  haveI : IsFractionRing (PreTilt O p) K := isFractionRing_of_ringEquiv e1 (fun _ => rfl)
  refine ⟨?_⟩
  show FractionRing (PreTilt O p) ≃+* K
  exact (IsLocalization.algEquiv (nonZeroDivisors (PreTilt O p))
    (FractionRing (PreTilt O p)) K).toRingEquiv

/-- The multiplicative ("sharp") side of the tilting correspondence: if the ring of integers `O`
is `p`-adically complete, there is a multiplicative map `♯ : O♭ → O` from the integral tilt
`PreTilt O p` to `O` which lifts the identification of `O♭/p♭` with `O/p` in degree `0`.

This is Mathlib's `PreTilt.untilt` together with `PreTilt.mk_untilt_eq_coeff_zero`. -/
theorem exists_sharp_multiplicative {O : Type*} [CommRing O] (p : ℕ) [Fact p.Prime]
    [Fact ¬ IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] :
    ∃ sharp : PreTilt O p →* O, ∀ x : PreTilt O p,
      Ideal.Quotient.mk (Ideal.span {(p : O)}) (sharp x) = PreTilt.coeff 0 x :=
  ⟨PreTilt.untilt, PreTilt.mk_untilt_eq_coeff_zero⟩

/-- **Scholze's tilting correspondence** for perfectoid fields.

For a field `K` with valuation `v : K → ℝ≥0`, ring of integers `O` and a prime `p` with
`v p ≠ 1`, the tilt `K♭ = Tilt K v O hv p` (the fraction field of the perfection of `O/p`) is:

* a field of characteristic `p`;
* perfect, i.e. its Frobenius `x ↦ x ^ p` is bijective;

and tilting is the identity on characteristic `p` inputs: if `K` itself is a perfect field of
characteristic `p`, then `K♭ ≃+* K`. -/
theorem scholze_perfectoid_tilt :
    (CharP (Tilt K v O hv p) p ∧ Function.Bijective fun x : Tilt K v O hv p => x ^ p) ∧
      (∀ (_ : CharP K p) (_ : Function.Surjective fun x : K => x ^ p),
        Nonempty (Tilt K v O hv p ≃+* K)) :=
  ⟨⟨charP_tilt v hv p, tilt_pow_bijective v hv p⟩, tilt_ringEquiv_self v hv p⟩

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

