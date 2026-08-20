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
