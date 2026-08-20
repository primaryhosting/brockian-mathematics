import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_ankeny_b_one_mod_eight (n q : ℕ) (hn : n % 8 = 1) (hq : Nat.Prime q)
    (hq1 : q % 4 = 1) (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) :
    ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (2 * q)] := by
  classical
  have hn_odd : Odd n := by
    have : n % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  have hn0 : n ≠ 0 := by
    intro h0; subst h0
    simp at hn

  have hq_odd : Odd q := by
    -- `q % 4 = 1` rules out `q = 2`, hence `q` is odd.
    have hq_ne2 : q ≠ 2 := by
      intro hq2; subst hq2
      simp at hq1
    exact hq.odd_of_ne_two hq_ne2

  -- Step 1: compute `J(q | n)` from the congruence `2*q ≡ -1 (mod n)`.
  have h2unit : IsUnit (2 : ZMod n) := GeometryOfNumbers.NumberTheory.zmod_isUnit_two_of_odd n hn_odd
  have h2q_mod_n : (2 * (q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] :=
    GeometryOfNumbers.NumberTheory.mul_int_modEq_neg_one_of_q_eq_neg_inv n 2 q h2unit (by simpa using hq_mod)

  have hJ_2q : J(2 * (q : ℤ) | n) = J(-1 | n) := by
    -- Jacobi symbol depends only on the numerator mod `n`.
    refine jacobiSym.mod_left' (a₁ := (2 * (q : ℤ))) (a₂ := (-1 : ℤ)) (b := n) ?_
    simpa using h2q_mod_n.eq

  have hn4 : n % 4 = 1 := by omega

  have hJ_neg_one : J(-1 | n) = (1 : ℤ) := by
    -- `J(-1 | n) = χ₄ n = 1` since `n % 4 = 1`.
    calc
      J(-1 | n) = ZMod.χ₄ n := jacobiSym.at_neg_one hn_odd
      _ = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hn4

  have hJ_two : J(2 | n) = (1 : ℤ) := by
    -- `J(2 | n) = χ₈ n = 1` since `n % 8 = 1`.
    calc
      J(2 | n) = ZMod.χ₈ n := jacobiSym.at_two hn_odd
      _ = (1 : ℤ) := by
        have hred : ZMod.χ₈ n = ZMod.χ₈ (n % 8 : ℕ) := by
          simpa using (ZMod.χ₈_nat_mod_eight n)
        have hval : ZMod.χ₈ (1 : ℕ) = (1 : ℤ) := by decide
        simpa [hred, hn] using hval

  have hJ_q : J((q : ℤ) | n) = (1 : ℤ) := by
    -- From `J(2*q|n) = J(2|n)*J(q|n)` and the computed values, solve for `J(q|n)`.
    have hmul : J((2 : ℤ) * (q : ℤ) | n) = J(2 | n) * J((q : ℤ) | n) := jacobiSym.mul_left 2 q n
    have : J(2 | n) * J((q : ℤ) | n) = (1 : ℤ) := by
      have : J((2 : ℤ) * (q : ℤ) | n) = (1 : ℤ) := by
        simpa [mul_assoc] using (hJ_2q.trans hJ_neg_one)
      simpa [hmul] using this
    have : (1 : ℤ) * J((q : ℤ) | n) = (1 : ℤ) := by simpa [hJ_two] using this
    simpa using this

  -- Step 2+: the remaining work is residue-agnostic once `J(q|n)=1` is known.
  exact exists_b_sq_congr_neg_of_jacobi_q_eq_one n q hn_odd hq hq1 hJ_q

/-- The Ankeny lattice `L = { (x,y,z) : x ≡ y (mod n), y ≡ bz (mod 2q) }`. -/
