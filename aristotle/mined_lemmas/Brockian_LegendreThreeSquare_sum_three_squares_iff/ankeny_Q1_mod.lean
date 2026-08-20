import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_Q1_mod (n q : ℕ) (b x y z : ℤ)
    (hnq : Nat.Coprime n q)
    (hq : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)])
    (hxy : x ≡ y [ZMOD (n : ℤ)])
    (hybz : y ≡ b * z [ZMOD (q : ℤ)])
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (q : ℤ)]) :
    ankeny_Q1 n q x y z ≡ 0 [ZMOD (n : ℤ) * (q : ℤ)] := by
  -- Part 1: mod `q`.
  have hQ_mod_q : ankeny_Q1 n q x y z ≡ 0 [ZMOD (q : ℤ)] := by
    have hy2 : y ^ 2 ≡ (b * z) ^ 2 [ZMOD (q : ℤ)] := hybz.pow 2
    have hy2' : y ^ 2 ≡ b ^ 2 * z ^ 2 [ZMOD (q : ℤ)] := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy2
    have hb_mul : b ^ 2 * z ^ 2 ≡ (-(n : ℤ)) * z ^ 2 [ZMOD (q : ℤ)] :=
      Int.ModEq.mul_right (z ^ 2) hb
    have hy_nz : y ^ 2 + (n : ℤ) * z ^ 2 ≡ 0 [ZMOD (q : ℤ)] := by
      have h1 :
          y ^ 2 + (n : ℤ) * z ^ 2 ≡ b ^ 2 * z ^ 2 + (n : ℤ) * z ^ 2 [ZMOD (q : ℤ)] :=
        hy2'.add (Int.ModEq.refl _)
      have h2 :
          b ^ 2 * z ^ 2 + (n : ℤ) * z ^ 2 ≡ (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 [ZMOD (q : ℤ)] :=
        hb_mul.add (Int.ModEq.refl _)
      have h3 : (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 = 0 := by ring
      exact h1.trans (h2.trans (by simpa [h3] using (Int.ModEq.refl (0 : ℤ))))
    have hqxx : (q : ℤ) * x ^ 2 ≡ 0 [ZMOD (q : ℤ)] := by
      refine (Int.modEq_zero_iff_dvd).2 ?_
      exact dvd_mul_right (q : ℤ) (x ^ 2)
    have : (q : ℤ) * x ^ 2 + (y ^ 2 + (n : ℤ) * z ^ 2) ≡ 0 [ZMOD (q : ℤ)] := by
      simpa [add_assoc, add_comm, add_left_comm] using (hqxx.add hy_nz)
    simpa [ankeny_Q1, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this

  -- Part 2: mod `n`.
  have hQ_mod_n : ankeny_Q1 n q x y z ≡ 0 [ZMOD (n : ℤ)] := by
    have hx2 : x ^ 2 ≡ y ^ 2 [ZMOD (n : ℤ)] := hxy.pow 2
    have hmul : (q : ℤ) * x ^ 2 ≡ (q : ℤ) * y ^ 2 [ZMOD (n : ℤ)] :=
      Int.ModEq.mul_left (q : ℤ) hx2
    have hq1 : (q : ℤ) + 1 ≡ 0 [ZMOD (n : ℤ)] := by
      -- add 1 to `q ≡ -1`.
      simpa [add_assoc, add_left_comm, add_comm] using (hq.add_right 1)
    have hq1y : ((q : ℤ) + 1) * (y ^ 2) ≡ 0 [ZMOD (n : ℤ)] := by
      -- `mul_right` yields `((q+1)*y^2) ≡ (0*y^2)`; normalize the RHS.
      simpa using (Int.ModEq.mul_right (y ^ 2) hq1)
    have hqy : (q : ℤ) * (y ^ 2) + (y ^ 2) ≡ 0 [ZMOD (n : ℤ)] := by
      have : (q : ℤ) * (y ^ 2) + (y ^ 2) = ((q : ℤ) + 1) * (y ^ 2) := by ring
      simpa [this] using hq1y
    have hnz : (n : ℤ) * (z ^ 2) ≡ 0 [ZMOD (n : ℤ)] := by
      refine (Int.modEq_zero_iff_dvd).2 ?_
      exact dvd_mul_right (n : ℤ) (z ^ 2)
    have hsum : (q : ℤ) * x ^ 2 + (y ^ 2) + (n : ℤ) * z ^ 2 ≡ 0 [ZMOD (n : ℤ)] := by
      -- replace `q*x^2` by `q*y^2`, then use `(q+1)*y^2 ≡ 0`.
      have h1 : (q : ℤ) * x ^ 2 + y ^ 2 ≡ (q : ℤ) * y ^ 2 + y ^ 2 [ZMOD (n : ℤ)] :=
        hmul.add (Int.ModEq.refl _)
      have h2 : (q : ℤ) * y ^ 2 + y ^ 2 + (n : ℤ) * z ^ 2 ≡ 0 [ZMOD (n : ℤ)] := by
        simpa [add_assoc] using (hqy.add hnz)
      exact (h1.add (Int.ModEq.refl _)).trans (by
        simpa [add_assoc, add_left_comm, add_comm] using h2)
    simpa [ankeny_Q1, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hsum

  -- CRT combine.
  have hmn : (n : ℤ).natAbs.Coprime (q : ℤ).natAbs := by
    simpa using hnq
  exact (Int.modEq_and_modEq_iff_modEq_mul (a := ankeny_Q1 n q x y z) (b := 0) (m := (n : ℤ))
    (n := (q : ℤ)) hmn).1 ⟨hQ_mod_n, hQ_mod_q⟩

/-- Any point in the Ankeny lattice satisfies `Q ≡ 0 (mod 2nq)`. -/
