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

theorem ord_divFun_finite (D : Divisor K) (q : FinitePlace K) :
    ord (some q) (divFun D) = D (some q) := by
  classical
  rw [ord_divFun]
  rw [Finset.sum_congr rfl (g := fun v => if v = some q then D v else 0) ?_]
  · rw [Finset.sum_ite_eq' D.support (some q) (fun v => D v)]
    by_cases h : some q ∈ D.support
    · simp [h]
    · simp only [h, if_false]
      exact (Finsupp.notMem_support_iff.1 h).symm
  · intro v _
    cases v with
    | none => simp [ord_finite_placeElt_infty]
    | some p =>
      rw [ord_placeElt_finite]
      by_cases h : p = q
      · subst h; simp
      · simp [h, Ne.symm h, Option.some_inj]

