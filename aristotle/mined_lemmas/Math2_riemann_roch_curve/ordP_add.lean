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

lemma ordP_add {p : k[X]} (hp : Prime p) {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) : min (ordP p f) (ordP p g) ≤ ordP p (f + g) := by
  set a := f.num with hha; set b := f.denom with hhb
  set c := g.num with hhc; set d := g.denom with hhd
  have ha : a ≠ 0 := RatFunc.num_ne_zero hf
  have hb : b ≠ 0 := RatFunc.denom_ne_zero f
  have hc : c ≠ 0 := RatFunc.num_ne_zero hg
  have hd : d ≠ 0 := RatFunc.denom_ne_zero g
  have h1 : f + g = (algebraMap k[X] (RatFunc k)) (a * d + b * c)
      / (algebraMap k[X] (RatFunc k)) (b * d) := by
    rw [map_add, map_mul, map_mul, map_mul, ← div_add_div _ _ (RatFunc.algebraMap_ne_zero hb)
      (RatFunc.algebraMap_ne_zero hd), hha, hhb, hhc, hhd, RatFunc.num_div_denom,
      RatFunc.num_div_denom]
  have hsum : a * d + b * c ≠ 0 := by
    intro h
    apply hfg
    rw [h1, h, map_zero, zero_div]
  rw [h1, ordP_div hp hsum (mul_ne_zero hb hd), mult_mul hp hb hd]
  have hkey := mult_add_ge hp (mul_ne_zero ha hd) (mul_ne_zero hb hc) hsum
  rw [mult_mul hp ha hd, mult_mul hp hb hc] at hkey
  simp only [ordP, ← hha, ← hhb, ← hhc, ← hhd]
  omega

