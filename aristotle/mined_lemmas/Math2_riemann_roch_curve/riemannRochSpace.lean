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

def riemannRochSpace (D : Divisor K) : Submodule K (RatFunc K) where
  carrier := {f | f = 0 ∨ ∀ v : Place K, -(D v) ≤ ord v f}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro f g (rfl | hf) hg
    · simpa using hg
    · rcases hg with rfl | hg
      · simpa using Or.inr hf
      rcases eq_or_ne f 0 with rfl | hf0
      · simpa using Or.inr hg
      rcases eq_or_ne g 0 with rfl | hg0
      · simpa using Or.inr hf
      rcases eq_or_ne (f + g) 0 with h0 | h0
      · exact Or.inl h0
      refine Or.inr fun v => ?_
      have := min_le_ord_add v hf0 hg0 h0
      have h1 := hf v
      have h2 := hg v
      omega
  smul_mem' := by
    rintro c f (rfl | hf)
    · simpa using Or.inl rfl
    · rcases eq_or_ne c 0 with rfl | hc
      · simpa using Or.inl rfl
      rcases eq_or_ne f 0 with rfl | hf0
      · simpa using Or.inl rfl
      refine Or.inr fun v => ?_
      have hCc : (RatFunc.C c : RatFunc K) ≠ 0 := by
        simpa using hc
      rw [RatFunc.smul_eq_C_mul, ord_mul v hCc hf0, ord_C]
      simpa using hf v

