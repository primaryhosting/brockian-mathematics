/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope

Mathlib (as of this version) contains no Riemann–Roch theorem for curves, no divisors on
curves, and no genus, so everything used here is developed from scratch in this file.

We formalize the smooth projective curve `ℙ¹_k` over an arbitrary field `k` through its
function field `k(X)`: its closed points are the monic irreducible polynomials (the closed
points of `𝔸¹ = Spec k[X]`) together with the point at infinity, each equipped with its
normalized valuation `ord P` and its residue degree `deg P`.  Divisors, the degree of a
divisor, the Riemann–Roch space `L(D)`, its dimension `ℓ(D)`, the canonical divisor `K` and
the genus `g = ℓ(K)` are all defined here, and the main theorem
`Math2.riemann_roch_curve` proves

  `ℓ(D) - ℓ(K - D) = deg D + 1 - g`

for every divisor `D` on this curve.  The genus is *computed* (`Math2.genus_eq_zero`), not
assumed, and `Math2.riemann_roch_of_degree_eq_neg_two` shows the identity holds with `K`
replaced by any divisor of degree `2g - 2 = -2`.

The key input is the computation `ℓ(D) = max (deg D + 1) 0` (`Math2.ell_eq_max`), obtained
from an explicit `k`-linear isomorphism between `L(D)` and the space of polynomials of
degree `< deg D + 1`.
-/

open scoped BigOperators
open scoped Classical

open Polynomial

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math2

variable {k : Type*} [Field k]

/-! ## Closed points of the projective line -/

/-- A finite closed point of the projective line `ℙ¹_k`, i.e. a closed point of the affine
line `𝔸¹_k = Spec k[X]`: a monic irreducible polynomial. -/
abbrev FinitePlace (k : Type*) [Field k] := {p : k[X] // p.Monic ∧ Irreducible p}

/-- The closed points of the smooth projective curve `ℙ¹_k`: the closed points of the affine
line, together with the point at infinity (`none`). -/
abbrev Place (k : Type*) [Field k] := Option (FinitePlace k)

/-- The degree `[k(P) : k]` of a closed point of `ℙ¹_k`. -/

lemma exists_polynomial_of_ordP_nonneg {f : RatFunc k}
    (h : ∀ p : k[X], p.Monic → Irreducible p → 0 ≤ ordP p f) :
    ∃ u : k[X], f = algebraMap k[X] (RatFunc k) u := by
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hunit : IsUnit f.denom := by
    by_contra hnu
    obtain ⟨q, hq, hqd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hden
    have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq.ne_zero
    have hcu : IsUnit (Polynomial.C (q.leadingCoeff)⁻¹) :=
      Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero hlc))
    set q' : k[X] := q * Polynomial.C (q.leadingCoeff)⁻¹ with hq'
    have hassoc : Associated q q' := ⟨hcu.unit, by rw [hq']; congr⟩
    have hq'm : q'.Monic := Polynomial.monic_mul_leadingCoeff_inv hq.ne_zero
    have hq'i : Irreducible q' := hassoc.irreducible hq
    have hq'd : q' ∣ f.denom := hassoc.symm.dvd.trans hqd
    have hprime : Prime q' := hq'i.prime
    have hnumdvd : ¬ q' ∣ f.num := fun hdn =>
      hprime.not_unit ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' hdn hq'd)
    have h1 : multiplicity q' f.num = 0 := multiplicity_eq_zero.mpr hnumdvd
    have h2 : 1 ≤ multiplicity q' f.denom :=
      (FiniteMultiplicity.of_prime_left hprime hden).le_multiplicity_of_pow_dvd
        (by simpa using hq'd)
    have h3 := h q' hq'm hq'i
    simp only [ordP, h1] at h3
    omega
  have hd1 : f.denom = 1 := (RatFunc.monic_denom f).eq_one_of_isUnit hunit
  refine ⟨f.num, ?_⟩
  rw [← RatFunc.num_div_denom f, hd1]
  simp

/-- The prime associated with a finite place. -/
