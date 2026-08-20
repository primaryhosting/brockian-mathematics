import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-! ## The definition -/

/-- A *betrothed* (quasi-amicable) pair: two positive integers each of whose sum of
divisors equals the sum of the two numbers plus one, i.e. `σ₁(m) = σ₁(n) = m + n + 1`. -/

lemma four_lt_abundancyBound_mul {m n : ℕ} (h : IsBetrothedPair m n)
    (hcop : Nat.Coprime m n) : 4 < abundancyBound (m * n) := by
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  have hm0 : m ≠ 0 := hm.ne'
  have hn0 : n ≠ 0 := hn.ne'
  have hmQ : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hnQ : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have h1 : ((m : ℚ) + n + 1) ≤ m * abundancyBound m := by
    have := sigma_one_le_mul_abundancyBound hm0
    rw [hsm] at this
    push_cast at this
    linarith
  have h2 : ((m : ℚ) + n + 1) ≤ n * abundancyBound n := by
    have := sigma_one_le_mul_abundancyBound hn0
    rw [hsn] at this
    push_cast at this
    linarith
  have hprod : ((m : ℚ) + n + 1) ^ 2 ≤ (m * n) * (abundancyBound m * abundancyBound n) := by
    have hpos : (0 : ℚ) ≤ (m : ℚ) + n + 1 := by linarith
    calc ((m : ℚ) + n + 1) ^ 2 = ((m : ℚ) + n + 1) * ((m : ℚ) + n + 1) := by ring
      _ ≤ ((m : ℚ) * abundancyBound m) * ((n : ℚ) * abundancyBound n) := by
          exact mul_le_mul h1 h2 hpos (le_trans hpos h1)
      _ = (m * n) * (abundancyBound m * abundancyBound n) := by ring
  have hgt : 4 * ((m : ℚ) * n) < ((m : ℚ) + n + 1) ^ 2 := by nlinarith [sq_nonneg ((m : ℚ) - n)]
  have hmn : (0 : ℚ) < (m : ℚ) * n := by positivity
  rw [abundancyBound_mul_of_coprime hm0 hn0 hcop]
  have : 4 * ((m : ℚ) * n) < ((m : ℚ) * n) * (abundancyBound m * abundancyBound n) := by
    linarith
  nlinarith [this]

/-! ## The main theorem -/

/-- **Hagis–Lord, Proposition 2 (second part).**  If `(m, n)` is a betrothed
(quasi-amicable) pair with `gcd(m, n) = 1` whose two members have the same parity, then
both members are odd and the product `m * n` has at least twenty-one distinct prime
factors.

This is the exact, unconditional statement.  It should be distinguished from the
*historical computational lower bounds* for betrothed pairs (searches by Hagis and Lord
and later authors show that no coprime betrothed pair exists below various computational
search limits, and give much larger numerical bounds); no such computational claim is
asserted or used here. -/
