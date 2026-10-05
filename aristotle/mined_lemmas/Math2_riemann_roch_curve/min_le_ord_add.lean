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

theorem min_le_ord_add (v : Place K) {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) : min (ord v f) (ord v g) ≤ ord v (f + g) := by
  cases v with
  | none =>
    have h := RatFunc.intDegree_add_le hg hfg
    simp only [ord_infty]
    omega
  | some p =>
    have hfn := RatFunc.num_ne_zero hf
    have hgn := RatFunc.num_ne_zero hg
    have hfd := RatFunc.denom_ne_zero f
    have hgd := RatFunc.denom_ne_zero g
    have hsum : f + g = algebraMap K[X] (RatFunc K) (f.num * g.denom + f.denom * g.num)
        / algebraMap K[X] (RatFunc K) (f.denom * g.denom) := by
      conv_lhs => rw [← RatFunc.num_div_denom f, ← RatFunc.num_div_denom g]
      rw [div_add_div _ _ (RatFunc.algebraMap_ne_zero hfd) (RatFunc.algebraMap_ne_zero hgd),
        map_add, map_mul, map_mul, map_mul]
    have hnum_ne : f.num * g.denom + f.denom * g.num ≠ 0 := by
      intro h
      apply hfg
      rw [hsum, h]
      simp
    rw [hsum, ord_finite_div p hnum_ne (mul_ne_zero hfd hgd)]
    have h1 : mult p (f.num * g.denom) = mult p f.num + mult p g.denom := mult_mul p hfn hgd
    have h2 : mult p (f.denom * g.num) = mult p f.denom + mult p g.num := mult_mul p hfd hgn
    have h3 := min_le_mult_add p hnum_ne
    have h4 : mult p (f.denom * g.denom) = mult p f.denom + mult p g.denom := mult_mul p hfd hgd
    simp only [ord_finite]
    rw [h1, h2] at h3
    omega

/-- A nonzero rational function all of whose orders at finite places are nonnegative is a
polynomial. -/
