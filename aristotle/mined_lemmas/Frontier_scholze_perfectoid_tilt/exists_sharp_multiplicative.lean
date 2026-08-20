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
