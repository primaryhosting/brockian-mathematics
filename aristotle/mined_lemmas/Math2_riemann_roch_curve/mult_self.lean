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

@[simp] theorem mult_self (p : FinitePlace K) : mult p (p : K[X]) = 1 := by
  have h := multiplicity_pow_self_of_prime p.prime 1
  rw [pow_one] at h
  rw [mult_of_ne_zero p p.ne_zero, h]
  simp

/-- The order of vanishing of a rational function at a place of `ℙ¹_K`.  At a finite place `p`
this is the multiplicity of `p` in the numerator minus that in the denominator; at the place at
infinity it is minus the degree.  By convention the order of `0` is `0`; the zero function is
treated separately everywhere. -/
