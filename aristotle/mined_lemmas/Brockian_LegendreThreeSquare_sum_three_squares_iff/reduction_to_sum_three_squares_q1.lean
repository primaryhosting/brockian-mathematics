import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma reduction_to_sum_three_squares_q1 (n q : ℕ) (x y z : ℤ)
    (h_ankeny : (q : ℤ) * x^2 + y^2 + (n : ℤ) * z ^ 2 = (n * q : ℤ))
    (hq_prime : Nat.Prime q) (hq1 : q % 4 = 1)
    (hq_mod : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)])
    (hn_sq : Squarefree n)
    (b : ℤ)
    (hxy : x ≡ y [ZMOD (n : ℤ)]) (hybz : y ≡ b * z [ZMOD (q : ℤ)])
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (q : ℤ)]) :
    ∃ u v : ℤ, (n : ℤ) = x^2 + u^2 + v^2 := by
  have h_eq : y^2 + (n : ℤ) * z^2 = (q : ℤ) * ((n : ℤ) - x^2) := by
    calc
      y^2 + (n : ℤ) * z^2
          = ((q : ℤ) * x^2 + y^2 + (n : ℤ) * z^2) - (q : ℤ) * x^2 := by ring
      _ = (n * q : ℤ) - (q : ℤ) * x^2 := by rw [h_ankeny]
      _ = (q : ℤ) * ((n : ℤ) - x^2) := by ring

  have h_diff_nonneg : 0 ≤ (n : ℤ) - x^2 := by
    have h_rhs : 0 ≤ y^2 + (n : ℤ) * z^2 := by
      apply add_nonneg (sq_nonneg y)
      apply mul_nonneg (Int.natCast_nonneg n) (sq_nonneg z)
    rw [h_eq] at h_rhs
    have hq_pos : 0 < (q : ℤ) := by
      have : 0 < q := hq_prime.pos
      exact_mod_cast this
    exact nonneg_of_mul_nonneg_right h_rhs hq_pos

  let K := ((n : ℤ) - x^2).natAbs
  have hK_eq : (K : ℤ) = (n : ℤ) - x^2 := Int.natAbs_of_nonneg h_diff_nonneg

  by_cases hK0 : K = 0
  · refine ⟨0, 0, ?_⟩
    have : (n : ℤ) = x ^ 2 := by
      have : (n : ℤ) - x ^ 2 = 0 := by simpa [hK0] using hK_eq.symm
      linarith
    simpa [this]
  ·
    have hK_sq_add_sq : ∃ u v : ℕ, K = u ^ 2 + v ^ 2 := by
      refine (Nat.eq_sq_add_sq_iff (n := K)).2 ?_
      intro p hpK hp4
      -- Q₁ parity kernel (currently a single lemma boundary).
      simpa using
        ankeny_even_padicValNat_of_mem_primeFactors_q1 (n := n) (q := q) (K := K) (p := p)
          (x := x) (y := y) (z := z) (b := b)
          hq1 hq_prime hq_mod hn_sq hK_eq (by
            -- cast `h_eq` into the expected `y^2 + n*z^2 = q*K` form
            simpa [hK_eq, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun t : ℤ => t) h_eq)
          hxy hybz hb hpK hp4

    obtain ⟨uN, vN, hK⟩ := hK_sq_add_sq
    refine ⟨(uN : ℤ), (vN : ℤ), ?_⟩
    have hKz : (K : ℤ) = (uN ^ 2 + vN ^ 2 : ℤ) := by exact_mod_cast hK
    have hn_int : (n : ℤ) = x ^ 2 + (K : ℤ) := by linarith [hK_eq]
    calc
      (n : ℤ) = x ^ 2 + (K : ℤ) := hn_int
      _ = x ^ 2 + (uN ^ 2 + vN ^ 2 : ℤ) := by simpa [hKz]
      _ = x ^ 2 + (uN : ℤ) ^ 2 + (vN : ℤ) ^ 2 := by simp [pow_two, add_assoc]

/-- Final theorem for `n ≡ 3 (mod 8)`. -/
