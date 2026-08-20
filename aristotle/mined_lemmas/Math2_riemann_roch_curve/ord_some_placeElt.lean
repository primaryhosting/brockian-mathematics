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

lemma ord_some_placeElt (q : FinitePlace k) (P : Place k) :
    ord (some q) (placeElt P) = if P = some q then 1 else 0 := by
  cases P with
  | none => simp [placeElt, ord, ordP]
  | some p =>
    rw [show placeElt (some p) = algebraMap k[X] (RatFunc k) p.1 from rfl]
    have : ord (some q) (algebraMap k[X] (RatFunc k) p.1)
        = (multiplicity q.1 p.1 : ℤ) := ordP_algebraMap q.prime p.2.2.ne_zero
    rw [this]
    by_cases h : p = q
    · subst h
      simp [multiplicity_self]
    · have hnd : ¬ (q.1 ∣ p.1) := by
        rintro ⟨c, hc⟩
        rcases p.2.2.isUnit_or_isUnit hc with h1 | h1
        · exact q.2.2.not_isUnit h1
        · exact h (Subtype.ext (Polynomial.eq_of_monic_of_associated q.2.1 p.2.1
            ⟨h1.unit, hc.symm⟩).symm)
      simp [multiplicity_eq_zero.mpr hnd, h]

/-- The rational function `∏ p ^ n_p` attached to a divisor `D = ∑ n_P · P` (the factor at
infinity is `1`). -/
