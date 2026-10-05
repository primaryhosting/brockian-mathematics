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

theorem ord_finite_div (p : FinitePlace K) {a b : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ord (some p) (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b)
      = mult p a - mult p b := by
  set f : RatFunc K := algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b with hf
  have hfne : f ≠ 0 :=
    div_ne_zero (RatFunc.algebraMap_ne_zero ha) (RatFunc.algebraMap_ne_zero hb)
  have key : f.num * b = a * f.denom := (RatFunc.num_mul_eq_mul_denom_iff hb).2 hf
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hfne
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hmul := congrArg (mult p) key
  rw [mult_mul p hnum hb, mult_mul p ha hden] at hmul
  simp only [ord_finite]
  omega

