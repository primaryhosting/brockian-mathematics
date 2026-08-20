/-
# Lagrange Four Squares
Category: Pure Mathematics
Target: Math.lagrange_four_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` commands to precede any module docstring (`/-! ... -/`),
-- so the header above is written as an ordinary block comment.

import Mathlib

/-!
This file contains a self-contained proof of Lagrange's four-square theorem, following
Lagrange's classical descent argument:

* `Math.euler_identity` : Euler's four-square identity;
* `Math.IsSum4.mul` : the sums of four squares are closed under multiplication;
* `Math.exists_mul_isSum4_of_prime` : some multiple `m * p` with `0 < m < p` of a prime `p`
  is a sum of four squares;
* `Math.isSum4_of_two_mul` and `Math.descent_odd` : the two descent steps;
* `Math.prime_isSum4` : every prime is a sum of four squares;
* `Math.lagrange_four_squares` : every natural number is a sum of four squares.
-/

namespace Math

/-- `IsSum4 n` states that the integer `n` is a sum of four integer squares. -/

private theorem descent_odd {p m : ℕ} (hp : p.Prime) (hm1 : 1 < m) (hmp : m < p)
    (hodd : m % 2 = 1) (h : IsSum4 ((m : ℤ) * p)) :
    ∃ r : ℕ, 0 < r ∧ r < m ∧ IsSum4 ((r : ℤ) * p) := by
  obtain ⟨a, b, c, d, h⟩ := h
  have hM0 : (0 : ℤ) < (m : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1.le
  have hModd : (m : ℤ) % 2 = 1 := by omega
  obtain ⟨A, α, haA, hA⟩ := exists_rep hM0 hModd a
  obtain ⟨B, β, hbB, hB⟩ := exists_rep hM0 hModd b
  obtain ⟨C, γ, hcC, hC⟩ := exists_rep hM0 hModd c
  obtain ⟨D, δ, hdD, hD⟩ := exists_rep hM0 hModd d
  subst haA hbB hcC hdD
  set M : ℤ := (m : ℤ) with hMdef
  set r : ℤ := p - 2 * (A * α + B * β + C * γ + D * δ) - M * (α ^ 2 + β ^ 2 + γ ^ 2 + δ ^ 2)
    with hrdef
  have hN : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = M * r := by rw [hrdef]; linear_combination h
  have hA4 := sq_lt_of_two_abs_lt hA
  have hB4 := sq_lt_of_two_abs_lt hB
  have hC4 := sq_lt_of_two_abs_lt hC
  have hD4 := sq_lt_of_two_abs_lt hD
  have hsqM : M ^ 2 = M * M := sq M
  have hr0 : 0 ≤ r := by
    have h2 : M * 0 ≤ M * r := by rw [← hN]; positivity
    exact le_of_mul_le_mul_left h2 hM0
  have hrM : r < M := by
    have h1 : M * r < M * M := by rw [← hN, ← hsqM]; linarith
    exact lt_of_mul_lt_mul_left h1 hM0.le
  have hrpos : 0 < r := by
    rcases hr0.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hz : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 0 := by rw [hN, ← h']; ring
      obtain ⟨hA0, hB0, hC0, hD0⟩ := eq_zero_of_sum_sq_eq_zero hz
      subst hA0 hB0 hC0 hD0
      have hp' : (p : ℤ) = (m : ℤ) * (α ^ 2 + β ^ 2 + γ ^ 2 + δ ^ 2) := by
        refine mul_left_cancel₀ (ne_of_gt hM0) ?_
        linear_combination -h
      have hmp' : m ∣ p := Int.natCast_dvd_natCast.mp ⟨α ^ 2 + β ^ 2 + γ ^ 2 + δ ^ 2, hp'⟩
      rcases hp.eq_one_or_self_of_dvd m hmp' with h1 | h1 <;> omega
  refine ⟨r.toNat, by omega, by omega, ?_⟩
  rw [Int.toNat_of_nonneg hr0]
  exact isSum4_of_euler_quotient (ne_of_gt hM0) hN h

/-- Some multiple `m * p`, with `0 < m < p`, of a prime `p` is a sum of four squares. -/
