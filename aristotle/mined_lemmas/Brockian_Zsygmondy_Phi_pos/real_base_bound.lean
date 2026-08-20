import Mathlib
namespace Brockian.Zsygmondy

open Polynomial

/-! ## Auxiliary results

The proof follows the classical cyclotomic-polynomial argument (Bang's theorem).
Write `Φ n a = eval (a : ℤ) (cyclotomic n ℤ)`.

* Any prime `q ∣ Φ n a` with `q ∤ n` is a primitive prime divisor of `aⁿ - 1`.
* If a prime `p ∣ Φ n a` divides `n`, writing `n = p ^ k * m` with `p ∤ m`, then the
  multiplicative order of `a` mod `p` is exactly `m`, hence `m ∣ p - 1`; in particular `p` is
  the largest prime factor of `n`, and `p ^ 2 ∤ Φ n a`.
* Consequently, if `Φ n a` has no prime factor coprime to `n`, then `Φ n a = p`.
* Finally `Φ n a > p`, a contradiction (except for `(a, n) = (2, 6)`).
-/

/-- The value of the `n`-th cyclotomic polynomial at a natural number `a`, as an integer. -/

lemma real_base_bound {p : ℕ} (hp : 5 ≤ p) {y : ℝ} (hy : 2 ≤ y) :
    (p : ℝ) ≤ (y ^ p - 1) / (y + 1) := by
  have hy1 : y + 1 > 0 := by linarith
  rw [le_div_iff₀ hy1]
  have hy2 : y ^ p ≥ 2 ^ p := by gcongr
  have hgeom : y ^ p - 1 = (y - 1) * ∑ i ∈ Finset.range p, y ^ i := by
    rw [mul_comm, geom_sum_mul]
  have hsum_bound : ∑ i ∈ Finset.range p, y ^ i ≥ ∑ i ∈ Finset.range 5, y ^ i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hp)
    intro x _ _
    exact pow_nonneg (by linarith : 0 ≤ y) x
  have hsum5 : ∑ i ∈ Finset.range 5, y ^ i = 1 + y + y^2 + y^3 + y^4 := by
    simp [Finset.sum_range_succ]
  have hprod : (y - 1) * (1 + y + y^2 + y^3 + y^4) = y^5 - 1 := by ring
  have hy5_bound : y ^ p - 1 ≥ y ^ 5 - 1 := by
    apply sub_le_sub_right
    exact pow_le_pow_right₀ (by linarith) hp
  have hy5_bound2 : y ^ 5 ≥ 5 * (y + 1) + 1 := by nlinarith [sq_nonneg y, sq_nonneg (y^2 - 2)]
  have aux : ∀ q : ℕ, 5 ≤ q → (y : ℝ) ^ q ≥ q * (y + 1) + 1 := by
    intro q hq
    have key : ∀ k : ℕ, (y : ℝ) ^ (5 + k) ≥ (5 + k) * (y + 1) + 1 := by
      intro k
      induction k with
      | zero => simp; exact hy5_bound2
      | succ k ih =>
        have h1 : y ^ (5 + (k + 1)) = y ^ (5 + k) * y := by ring
        have h2 : y ^ (5 + k) * y ≥ ((5 + k) * (y + 1) + 1) * y := by nlinarith
        have h3 : ((5 + k) * (y + 1) + 1) * y = (5 + k) * y * (y + 1) + y := by ring
        have hy2 : y ^ 2 ≥ 4 := by nlinarith
        have h4 : (5 + (k : ℝ)) * y ^ 2 ≥ 7 + k := by nlinarith
        have h5 : (5 + k) * y * (y + 1) + y ≥ (6 + k) * (y + 1) + 1 := by nlinarith
        have h8 : (5 : ℝ) + ↑(k + 1) = 6 + k := by push_cast; ring
        rw [h8]
        linarith
    have heq : q = 5 + (q - 5) := by omega
    rw [heq]
    simpa using key (q - 5)
  have := aux p hp
  linarith

/-- The case `m = 1`: `Φ_p(y) = 1 + y + ⋯ + y ^ (p - 1) ≥ 2 ^ p - 1 > p`. -/
