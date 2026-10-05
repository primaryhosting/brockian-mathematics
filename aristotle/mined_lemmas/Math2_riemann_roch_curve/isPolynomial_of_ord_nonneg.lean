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

theorem isPolynomial_of_ord_nonneg {f : RatFunc K} (hf : f ≠ 0)
    (h : ∀ p : FinitePlace K, 0 ≤ ord (some p) f) :
    ∃ a : K[X], f = algebraMap K[X] (RatFunc K) a := by
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  by_cases hu : IsUnit f.denom
  · refine ⟨f.num, ?_⟩
    have h1 : f.denom = 1 := (RatFunc.monic_denom f).eq_one_of_isUnit hu
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [h1]
    simp
  · exfalso
    obtain ⟨r, hr, hrdvd⟩ := WfDvdMonoid.exists_irreducible_factor hu hden
    have hr0 : r ≠ 0 := hr.ne_zero
    set p : K[X] := r * Polynomial.C r.leadingCoeff⁻¹ with hp
    have hpm : p.Monic := Polynomial.monic_mul_leadingCoeff_inv hr0
    have hassoc : Associated r p := by
      have hcu : IsUnit (Polynomial.C r.leadingCoeff⁻¹) :=
        isUnit_C.2 (isUnit_iff_ne_zero.2 (by
          simpa [inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using hr0))
      obtain ⟨u, hu'⟩ := hcu
      exact ⟨u, by rw [hu', hp]⟩
    have hpi : Irreducible p := hassoc.irreducible hr
    have hpdvd : p ∣ f.denom := (hassoc.dvd_iff_dvd_left).1 hrdvd
    have hP := h ⟨p, hpm, hpi⟩
    have h1 : 1 ≤ mult ⟨p, hpm, hpi⟩ f.denom := by
      have hpos : 0 < multiplicity p f.denom := multiplicity_pos_of_dvd hpdvd
      rw [mult_of_ne_zero _ hden]
      exact_mod_cast hpos
    have h2 : mult ⟨p, hpm, hpi⟩ f.num = 0 := by
      rw [mult_of_ne_zero _ (RatFunc.num_ne_zero hf)]
      simp only [Nat.cast_eq_zero]
      refine multiplicity_eq_zero.2 fun hdvd => ?_
      exact hpi.not_isUnit ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' hdvd hpdvd)
    rw [ord_finite] at hP
    omega

end Math2

end

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

