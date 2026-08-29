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

theorem mult_eq_zero_of_ne (p q : FinitePlace K) (h : p ≠ q) : mult p (q : K[X]) = 0 := by
  rw [mult_of_ne_zero p q.ne_zero]
  simp only [Nat.cast_eq_zero]
  refine multiplicity_eq_zero.2 fun hdvd => h (FinitePlace.ext ?_)
  exact Polynomial.eq_of_monic_of_associated p.2.1 q.2.1 (p.2.2.associated_of_dvd q.2.2 hdvd)

