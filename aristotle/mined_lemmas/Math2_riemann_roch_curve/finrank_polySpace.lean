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

theorem finrank_polySpace (m : ℕ) : Module.finrank K (polySpace K m) = m := by
  have hinj : Function.Injective (Algebra.linearMap K[X] (RatFunc K)) := by
    intro a b hab
    exact RatFunc.algebraMap_injective K (by simpa using hab)
  have e : (Polynomial.degreeLT K m) ≃ₗ[K] (polySpace K m) :=
    Submodule.equivMapOfInjective _ hinj _
  rw [← e.finrank_eq, (Polynomial.degreeLTEquiv K m).finrank_eq, Module.finrank_fin_fun]

/-- The key structural result: `L(D)` is obtained from the space of polynomials of degree
`≤ deg D` by dividing by the function `divFun D`. -/
