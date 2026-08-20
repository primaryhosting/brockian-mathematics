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

theorem exists_mul_isSum4_of_prime {p : ℕ} (hp : p.Prime) :
    ∃ m : ℕ, 0 < m ∧ m < p ∧ IsSum4 ((m : ℤ) * p) := by
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨A, B, hAB⟩ := ZMod.sq_add_sq p (-1)
  set a : ℤ := A.valMinAbs with hadef
  set b : ℤ := B.valMinAbs with hbdef
  have hA : a.natAbs ≤ p / 2 := ZMod.natAbs_valMinAbs_le A
  have hB : b.natAbs ≤ p / 2 := ZMod.natAbs_valMinAbs_le B
  have hdvd : (p : ℤ) ∣ a ^ 2 + b ^ 2 + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hadef, hbdef, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs, hAB]
    ring
  obtain ⟨t, ht⟩ := hdvd
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have ht0 : 0 < t := by
    rcases lt_trichotomy t 0 with h | h | h
    · nlinarith [sq_nonneg a, sq_nonneg b]
    · nlinarith [sq_nonneg a, sq_nonneg b]
    · exact h
  have hk : 2 * ((p / 2 : ℕ) : ℤ) ≤ (p : ℤ) := by
    have := Nat.div_mul_le_self p 2
    push_cast
    omega
  have haa : a ^ 2 ≤ ((p / 2 : ℕ) : ℤ) ^ 2 := by
    have h1 : |a| ≤ ((p / 2 : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hA
    nlinarith [abs_nonneg a, sq_abs a]
  have hbb : b ^ 2 ≤ ((p / 2 : ℕ) : ℤ) ^ 2 := by
    have h1 : |b| ≤ ((p / 2 : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hB
    nlinarith [abs_nonneg b, sq_abs b]
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hlt : (p : ℤ) * t < (p : ℤ) * p := by
    rw [← ht]
    nlinarith [Nat.cast_nonneg (α := ℤ) (p / 2)]
  have htp : t < p := lt_of_mul_lt_mul_left hlt hp0.le
  refine ⟨t.toNat, by omega, by omega, a, b, 1, 0, ?_⟩
  rw [Int.toNat_of_nonneg ht0.le]
  linarith [ht]

/-- Descent: if some `m * p` with `0 < m < p` is a sum of four squares, then so is `p`. -/
