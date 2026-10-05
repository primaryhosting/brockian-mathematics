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

theorem ell_eq (D : Divisor K) : (ell D : ℤ) = max (deg D + 1) 0 := by
  have hne : divFun D ≠ 0 := divFun_ne_zero D
  have hinj : Function.Injective (LinearMap.mulRight K (divFun D)⁻¹) := by
    intro x y hxy
    simp only [LinearMap.mulRight_apply] at hxy
    exact mul_right_cancel₀ (inv_ne_zero hne) hxy
  have e : (polySpace K (deg D + 1).toNat) ≃ₗ[K]
      (Submodule.map (LinearMap.mulRight K (divFun D)⁻¹) (polySpace K (deg D + 1).toNat)) :=
    Submodule.equivMapOfInjective _ hinj _
  have : ell D = (deg D + 1).toNat := by
    rw [ell, riemannRochSpace_eq_map D, ← e.finrank_eq, finrank_polySpace]
  rw [this]
  omega

end Math2

end

import Mathlib

/-!
# Places and orders of vanishing on the projective line

This file develops the elementary valuation theory of the rational function field `K(x)`,
i.e. of the smooth projective curve `ℙ¹_K`:

* `Math2.FinitePlace K` : the finite (closed) points of `ℙ¹_K`, i.e. the monic irreducible
  polynomials of `K[X]`;
* `Math2.Place K` : all closed points, i.e. the finite ones together with the point at
  infinity (`none`);
* `Math2.ord v f` : the order of vanishing of a rational function `f` at the place `v`.
-/

open Polynomial

noncomputable section

namespace Math2

variable {K : Type*} [Field K]

/-- The finite closed points of the projective line over `K`, i.e. the monic irreducible
polynomials over `K`. -/
abbrev FinitePlace (K : Type*) [Field K] : Type _ := {p : K[X] // p.Monic ∧ Irreducible p}

/-- The closed points of the projective line over `K`: the finite places together with the
point at infinity, denoted `none`. -/
abbrev Place (K : Type*) [Field K] : Type _ := Option (FinitePlace K)

namespace FinitePlace

