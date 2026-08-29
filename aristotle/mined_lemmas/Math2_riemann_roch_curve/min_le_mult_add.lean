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

theorem min_le_mult_add (p : FinitePlace K) {a b : K[X]} (hab : a + b ≠ 0) :
    min (mult p a) (mult p b) ≤ mult p (a + b) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have h := @min_le_emultiplicity_add _ _ (p : K[X]) a b
  rw [(finiteMultiplicity_of_ne_zero p ha).emultiplicity_eq_multiplicity,
    (finiteMultiplicity_of_ne_zero p hb).emultiplicity_eq_multiplicity,
    (finiteMultiplicity_of_ne_zero p hab).emultiplicity_eq_multiplicity] at h
  have h' : min (multiplicity (p : K[X]) a) (multiplicity (p : K[X]) b)
      ≤ multiplicity (p : K[X]) (a + b) := by
    have : ((min (multiplicity (p : K[X]) a) (multiplicity (p : K[X]) b) : ℕ) : ℕ∞)
        ≤ ((multiplicity (p : K[X]) (a + b) : ℕ) : ℕ∞) := by
      simpa [Nat.cast_min] using h
    exact_mod_cast this
  rw [mult_of_ne_zero p ha, mult_of_ne_zero p hb, mult_of_ne_zero p hab]
  exact_mod_cast h'

