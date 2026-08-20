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
