import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma sum_three_squares_of_five_mod_eight_squarefree (m : ℕ) (hm5 : m % 8 = 5) (hm_sq : Squarefree m) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = m := by
  -- Q₁ route: choose `q ≡ -1 (mod m)` and `b^2 ≡ -m (mod q)`, run the Minkowski step producing
  -- `q*x^2 + y^2 + m*z^2 = m*q`, then descend to a three-squares representation of `m`.
  have hm4 : m % 4 = 1 := by omega
  obtain ⟨q, hq_prime, hq1, hq_mod, b, hb⟩ :=
    exists_prime_one_mod_four_and_modEq_neg_one_and_b_sq_congr_neg_mod_q m hm4
  have hm_pos : 0 < m := by omega

  have hmq : Nat.Coprime m q := by
    have hqm : Nat.Coprime q m := by
      refine (hq_prime.coprime_iff_not_dvd).2 ?_
      intro hq_dvd_m
      have hm_dvd_q1 : (m : ℤ) ∣ (q : ℤ) + 1 := by
        have h' : (m : ℤ) ∣ (q : ℤ) - (-1 : ℤ) := (Int.modEq_iff_dvd).1 (by
          simpa using hq_mod.symm)
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h'
      have hq_dvd_mz : (q : ℤ) ∣ (m : ℤ) := by
        rcases hq_dvd_m with ⟨k, hk⟩
        refine ⟨(k : ℤ), ?_⟩
        exact_mod_cast hk
      have hq_dvd_q1 : (q : ℤ) ∣ (q : ℤ) + 1 := Int.dvd_trans hq_dvd_mz hm_dvd_q1
      have hq_dvd_1 : (q : ℤ) ∣ (1 : ℤ) := by
        have hq_dvd_q : (q : ℤ) ∣ (q : ℤ) := ⟨1, by ring⟩
        have : (q : ℤ) ∣ ((q : ℤ) + 1) - (q : ℤ) := Int.dvd_sub hq_dvd_q1 hq_dvd_q
        simpa using this
      have hq_unit : IsUnit (q : ℤ) := isUnit_of_dvd_one hq_dvd_1
      have hq_one : (q : ℤ) = 1 ∨ (q : ℤ) = -1 := by
        simpa [Int.isUnit_iff] using hq_unit
      cases hq_one with
      | inl h1 =>
          have : q = 1 := by exact_mod_cast h1
          exact hq_prime.ne_one this
      | inr hneg1 =>
          have hnonneg : (0 : ℤ) ≤ (q : ℤ) := by exact_mod_cast (Nat.zero_le q)
          -- Rewrite the nonnegativity fact using `q = -1`.
          rw [hneg1] at hnonneg
          have : (0 : ℤ) ≤ (-1 : ℤ) := hnonneg
          omega
    exact hqm.symm

  have hq_modZ : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (m : ℤ)] := by simpa using hq_mod

  obtain ⟨x, y, z, hQ, _hxyz_ne, hxy, hybz⟩ :=
    exists_ankeny_representation_q1 m q b hm_pos hq_prime hmq hq1 hq_modZ hb

  have hQ' : (q : ℤ) * x ^ 2 + y ^ 2 + (m : ℤ) * z ^ 2 = (m * q : ℤ) := by
    simpa [ankeny_Q1, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hQ

  obtain ⟨u, v, hm_int⟩ :=
    _root_.GeometryOfNumbers.reduction_to_sum_three_squares_q1 (n := m) (q := q) (x := x) (y := y) (z := z)
      hQ' hq_prime hq1 hq_modZ hm_sq b hxy hybz hb

  refine ⟨x.natAbs, u.natAbs, v.natAbs, ?_⟩
  zify
  simp [sq_abs, hm_int]

