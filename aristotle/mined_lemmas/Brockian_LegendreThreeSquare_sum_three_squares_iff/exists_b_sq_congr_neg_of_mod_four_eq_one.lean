import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_b_sq_congr_neg_of_mod_four_eq_one
    (n : ℕ) (hn4 : n % 4 = 1) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (2 * q)] := by
  classical
  have hn_odd : Odd n := by
    -- `n % 4 = 1` implies `n` odd.
    have : n % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  -- We want this with the same elaboration as `(r : ZMod n)` when `r = 1`.
  have h1 : IsUnit ((1 : ℕ) : ZMod n) := by
    simpa using (isUnit_one : IsUnit (1 : ZMod n))
  obtain ⟨q, hqp, hq1, hq_mod⟩ := exists_prime_one_mod_four_and_eq_neg_inv n 1 hn_odd h1
  -- Show `J(q|n) = 1` by reducing to `J(-1|n)`.
  have hq_modEq : ((q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] := by
    -- With `r = 1`, `1*q ≡ -1 (mod n)`.
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
  have := exists_b_sq_congr_neg_of_jacobi_q_eq_one n q hn_odd hqp hq1 hJ_q
  exact ⟨q, hqp, hq1, this⟩

/-- A packaging lemma for the `n % 8 = 5` (“`n % 4 = 1`”) branch:

We can pick a prime `q ≡ 1 (mod 4)` with `q ≡ -1 (mod n)`, and produce a square root of `-n` modulo `q`.

This is exactly the congruence interface needed for the `Q₁ = qx² + y² + nz²` variant:
- the `q ≡ -1 (mod n)` part is the `mod n` cancellation under `x ≡ y`,
- the `b² ≡ -n (mod q)` part is the `mod q` cancellation under `y ≡ b z`.
-/
