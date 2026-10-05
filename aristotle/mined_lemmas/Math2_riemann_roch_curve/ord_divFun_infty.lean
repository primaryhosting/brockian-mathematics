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

theorem ord_divFun_infty (D : Divisor K) :
    ord (none : Place K) (divFun D) = D none - deg D := by
  classical
  rw [ord_divFun]
  have : ∀ v ∈ D.support, D v * ord (none : Place K) (placeElt v)
      = -(D v * degPlace v) + (if v = none then D v else 0) := by
    intro v _
    rw [ord_placeElt_infty]
    by_cases h : v = none <;> simp [h] <;> ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
    Finset.sum_ite_eq' D.support none (fun v => D v)]
  have hdeg : deg D = ∑ v ∈ D.support, D v * degPlace v := rfl
  by_cases h : (none : Place K) ∈ D.support
  · simp [h, hdeg]
    ring
  · simp only [h, if_false]
    rw [Finsupp.notMem_support_iff.1 h]
    simp [hdeg]

/-- The space of polynomials of degree `< m`, viewed inside the rational function field. -/
