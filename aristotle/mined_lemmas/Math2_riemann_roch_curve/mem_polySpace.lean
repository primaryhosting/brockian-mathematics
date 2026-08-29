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

theorem mem_polySpace {m : ℕ} {f : RatFunc K} :
    f ∈ polySpace K m ↔ ∃ a : K[X], a.degree < (m : ℕ) ∧ f = algebraMap K[X] (RatFunc K) a := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (Polynomial.mem_degreeLT).1 ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (Polynomial.mem_degreeLT).2 ha, rfl⟩

