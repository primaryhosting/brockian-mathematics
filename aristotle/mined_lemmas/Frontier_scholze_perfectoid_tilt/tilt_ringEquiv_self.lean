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
