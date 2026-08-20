import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma reduction_to_sum_three_squares (n q : ℕ) (x y z : ℤ)
    (h_ankeny : 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q)
    (hq_prime : Nat.Prime q) (_hq1 : q % 4 = 1) (_hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹)
    (hn_odd : Odd n) (hn_sq : Squarefree n)
    (b : ℤ)
    (hxy : x ≡ y [ZMOD (n : ℤ)]) (hybz : y ≡ b * z [ZMOD (2 * q : ℤ)]) :
    ∃ u v : ℤ, n = x^2 + u^2 + v^2 := by
  have h_eq : y^2 + n * z^2 = 2 * q * (n - x^2) := by
    calc y^2 + n * z^2 = (2 * q * x^2 + y^2 + n * z^2) - 2 * q * x^2 := by ring
      _ = 2 * n * q - 2 * q * x^2 := by rw [h_ankeny]
      _ = 2 * q * (n - x^2) := by ring

  -- Show n - x^2 >= 0
  have h_diff_nonneg : 0 ≤ n - x^2 := by
    have h_rhs : 0 ≤ y^2 + n * z^2 := by
      apply add_nonneg (sq_nonneg y)
      apply mul_nonneg (Int.natCast_nonneg n) (sq_nonneg z)
    rw [h_eq] at h_rhs
    have h2q : 0 < (2 * q : ℤ) := by
      have hq_pos : 0 < q := hq_prime.pos
      norm_cast; linarith
    exact nonneg_of_mul_nonneg_right h_rhs h2q

  let K := (n - x^2).natAbs
  have hK_eq : (K : ℤ) = n - x^2 := Int.natAbs_of_nonneg h_diff_nonneg

  -- At this point we want to show `K` is a sum of two squares; then `n = x^2 + K`.
  --
  by_cases hK0 : K = 0
  · -- Then `n = x^2`, hence trivially a sum of three squares.
    refine ⟨0, 0, ?_⟩
    -- From `K = 0` and `hK_eq : (K:ℤ)=n-x^2`.
    have : (n : ℤ) = x ^ 2 := by
      -- `n - x^2 = 0`
      have : (n : ℤ) - x ^ 2 = 0 := by
        simpa [hK0] using hK_eq.symm
      linarith
    simpa [this]
  ·
    -- Nontrivial case: `K ≠ 0`. We now follow the *intended* (Ankeny-style) structure:
    -- use `Nat.eq_sq_add_sq_iff` to prove `K` is a sum of two squares by ruling out primes
    -- `≡ 3 (mod 4)` appearing to odd exponent in `K`.
    --
    -- The main local ingredient (for a fixed prime `p ≡ 3 (mod 4)` dividing `K`) is that,
    -- reducing the identity `y^2 + n*z^2 = 2*q*K` modulo `p` and using `n ≡ x^2 (mod p)`
    -- yields an equation of the form `A^2 = -B^2` in `ZMod p`. Since `p % 4 = 3`,
    -- `ZMod.mod_four_ne_three_of_sq_eq_neg_sq'` forces `B = 0`, hence `A = 0`,
    -- which can be bootstrapped to show `p^2 ∣ K` and thus `Even (padicValNat p K)`.
    have hK_sq_add_sq : ∃ u v : ℕ, K = u ^ 2 + v ^ 2 := by
      -- Number theory kernel:
      -- use `Nat.eq_sq_add_sq_iff` (Mathlib.NumberTheory.SumTwoSquares), which reduces the goal to
      -- a parity statement about primes `p ≡ 3 (mod 4)` dividing `K`.
      refine (Nat.eq_sq_add_sq_iff (n := K)).2 ?_
      intro p hpK hp4
      simpa using
        ankeny_even_padicValNat_of_mem_primeFactors (n := n) (q := q) (K := K) (p := p)
          (x := x) (y := y) (z := z) (b := b)
          hn_odd _hq1 _hq_mod hq_prime hn_sq hK_eq (by
            -- Rewrite into the form expected by `ankeny_even_padicValNat_of_mem_primeFactors`.
            -- `h_eq : y^2 + n*z^2 = 2*q*(n - x^2)`
            simpa [hK_eq, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun t : ℤ => t) h_eq)
          hxy hybz hpK hp4

    obtain ⟨uN, vN, hK⟩ := hK_sq_add_sq
    refine ⟨(uN : ℤ), (vN : ℤ), ?_⟩
    have hKz : (K : ℤ) = (uN ^ 2 + vN ^ 2 : ℤ) := by
      exact_mod_cast hK
    -- `n = x^2 + K = x^2 + u^2 + v^2`.
    have hn_int : (n : ℤ) = x ^ 2 + (K : ℤ) := by
      -- `K = n - x^2`
      linarith [hK_eq]
    calc
      (n : ℤ) = x ^ 2 + (K : ℤ) := hn_int
      _ = x ^ 2 + (uN ^ 2 + vN ^ 2 : ℤ) := by simpa [hKz]
      _ = x ^ 2 + (uN : ℤ) ^ 2 + (vN : ℤ) ^ 2 := by
        -- normalize casts/powers
        simp [pow_two, add_assoc]

/-!
### Q₁ reduction: `q*x^2 + y^2 + n*z^2 = n*q` ⇒ `n = x^2 + u^2 + v^2`

This mirrors `reduction_to_sum_three_squares`, but the “special representation” comes from the Q₁
Minkowski route, and the divisibility identity is `y^2 + n*z^2 = q*(n - x^2)`.

We keep the same invariant \(K := (n - x^2).natAbs\) and the same endpoint: prove `K` is a sum of
two squares via `Nat.eq_sq_add_sq_iff`.
-/
