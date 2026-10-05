import RequestProject.Places

/-!
# Divisors, Riemann–Roch spaces and their dimensions on the projective line

* `Math2.Divisor K` : divisors on `ℙ¹_K`, i.e. finitely supported `ℤ`-valued functions on the
  set of closed points;
* `Math2.deg D` : the degree of a divisor;
* `Math2.riemannRochSpace D` : the Riemann–Roch space `L(D) = {f : ord_v f ≥ -D v for all v}`;
* `Math2.ell D` : its dimension `ℓ(D)` over `K`.

The main result of this file is `Math2.ell_eq`: `ℓ(D) = max (deg D + 1) 0`.
-/

open Polynomial

noncomputable section

namespace Math2

variable {K : Type*} [Field K]

/-- The degree of a closed point of `ℙ¹_K`: the degree of the corresponding monic irreducible
polynomial, resp. `1` for the point at infinity. -/

theorem ord_divFun (w : Place K) (D : Divisor K) :
    ord w (divFun D) = ∑ v ∈ D.support, D v * ord w (placeElt v) := by
  rw [divFun, ord_prod w _ _ fun v _ => zpow_ne_zero _ (placeElt_ne_zero v)]
  exact Finset.sum_congr rfl fun v _ => ord_zpow w (placeElt_ne_zero v) (D v)

