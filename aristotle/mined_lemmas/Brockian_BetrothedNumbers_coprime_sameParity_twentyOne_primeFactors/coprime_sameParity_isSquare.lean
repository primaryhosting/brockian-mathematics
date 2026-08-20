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

theorem coprime_sameParity_isSquare {m n : ℕ}
    (h : IsBetrothedPair m n) (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    IsSquare m ∧ IsSquare n := by
  obtain ⟨hmodd, hnodd, -⟩ := coprime_sameParity_twentyOne_primeFactors h hcop hpar
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  have hsum : Odd (m + n + 1) := by
    rw [Nat.odd_iff] at *
    omega
  refine ⟨(odd_sigma_one_iff hm.ne' hmodd).mp ?_, (odd_sigma_one_iff hn.ne' hnodd).mp ?_⟩
  · rw [hsm]; exact hsum
  · rw [hsn]; exact hsum

/-- Sanity check: betrothed pairs do exist, e.g. `(48, 75)`; this pair is coprime but its
members have different parities, so it is not covered by the theorem above.  Indeed no
coprime same-parity betrothed pair is known: the historical computational searches
(Hagis–Lord and later authors) have found none, but those are *computational* results and
are deliberately not asserted here. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> decide

end Brockian.BetrothedNumbers

