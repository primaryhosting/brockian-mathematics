import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_prime_one_mod_four_and_modEq_neg_one_and_b_sq_congr_neg_mod_q
    (n : ℕ) (hn4 : n % 4 = 1) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q % 4 = 1 ∧
      ((q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] ∧
      ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (q : ℤ)] := by
  classical
  have hn_odd : Odd n := by
    have : n % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  have h1 : IsUnit ((1 : ℕ) : ZMod n) := by
    simpa using (isUnit_one : IsUnit (1 : ZMod n))
  obtain ⟨q, hqp, hq1, hq_mod⟩ := exists_prime_one_mod_four_and_eq_neg_inv n 1 hn_odd h1
  have hq_modEq : ((q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] := by
    have : ((1 : ℤ) * (q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] :=
      GeometryOfNumbers.NumberTheory.mul_int_modEq_neg_one_of_q_eq_neg_inv n 1 q (by simpa using h1) (by simpa using hq_mod)
    simpa using this
  have hJ_q : J((q : ℤ) | n) = (1 : ℤ) := by
    have : J((q : ℤ) | n) = J(-1 | n) := by
      refine jacobiSym.mod_left' (a₁ := (q : ℤ)) (a₂ := (-1 : ℤ)) (b := n) ?_
      simpa using hq_modEq.eq
    have hJ_neg_one : J(-1 | n) = (1 : ℤ) := by
      calc
        J(-1 | n) = ZMod.χ₄ n := jacobiSym.at_neg_one hn_odd
        _ = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hn4
    simpa [hJ_neg_one] using this
  obtain ⟨b, hb2⟩ := exists_b_sq_congr_neg_of_jacobi_q_eq_one n q hn_odd hqp hq1 hJ_q
  -- Reduce modulo `q` (from the stronger statement modulo `2*q`).
  have hq_dvd_2q : (q : ℤ) ∣ (2 * q : ℤ) := by
    simpa [mul_comm] using (dvd_mul_left (q : ℤ) (2 : ℤ))
  have hbq : b ^ 2 ≡ - (n : ℤ) [ZMOD (q : ℤ)] := Int.ModEq.of_dvd hq_dvd_2q hb2
  exact ⟨q, hqp, hq1, hq_modEq, ⟨b, hbq⟩⟩

/-- Existence of `b` such that `b² ≡ -n (mod 2q)` (Ankeny, `n % 8 = 3` specialization). -/
