import RequestProject.BelyiPoly

/-!
# Belyi polynomials for finite sets of rational points

A polynomial `f ∈ ℚ[X]` is *Belyi* if it is non-constant and all of its finite critical values
(computed over `ℂ`) lie in `{0, 1}`; viewed as a map `ℙ¹ → ℙ¹` such an `f` is ramified only
above `{0, 1, ∞}`.

The main result of this file is `Math2.exists_belyiPolynomial_of_rat`: for every finite set of
rational numbers there is a Belyi polynomial taking each of them to `0` or `1`.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial

/-- `f` is a Belyi polynomial: non-constant, with all finite critical values in `{0, 1}`. -/

lemma exists_num_den {lam : ℚ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℚ) / ((m : ℚ) + (n : ℚ)) = lam := by
  refine ⟨lam.num.toNat, lam.den - lam.num.toNat, ?_, ?_, ?_⟩
  · have : 0 < lam.num := Rat.num_pos.2 h0
    omega
  · have hnum : 0 < lam.num := Rat.num_pos.2 h0
    have : lam.num < (lam.den : ℤ) := Rat.lt_one_iff_num_lt_denom.mp h1
    omega
  · have hnum : 0 < lam.num := Rat.num_pos.2 h0
    have hlt : lam.num < (lam.den : ℤ) := Rat.lt_one_iff_num_lt_denom.mp h1
    have hsum : (lam.num.toNat : ℚ) + ((lam.den - lam.num.toNat : ℕ) : ℚ) = (lam.den : ℚ) := by
      have : lam.num.toNat ≤ lam.den := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hsum]
    have hnum' : (lam.num.toNat : ℚ) = (lam.num : ℚ) := by
      have : (lam.num.toNat : ℤ) = lam.num := Int.toNat_of_nonneg hnum.le
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) this
    rw [hnum']
    exact Rat.num_div_den lam

/-- Values of `f ∈ ℚ[X]` at rational points, transported to `ℂ`. -/
