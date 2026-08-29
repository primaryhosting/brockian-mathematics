import Mathlib
/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose
divisor sums equals the sum of the pair plus one. -/

lemma card_primeFactors_ge_of_odd_abundant {N : ℕ} (hN : N ≠ 0) (hodd : Odd N)
    (habund : 4 * N ≤ sigma 1 N) : 21 ≤ N.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hcard : N.primeFactors.card ≤ 20 := by omega
  have hp : ∀ p ∈ N.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h3 : ∀ p ∈ N.primeFactors, 3 ≤ p := by
    intro p hpm
    have hpp := Nat.prime_of_mem_primeFactors hpm
    have hp2 := hpp.two_le
    have := Nat.odd_iff.mp (odd_of_mem_primeFactors hodd hpm)
    omega
  have hlt := prod_abFactor_lt_four N.primeFactors hp h3 hcard
  have hle := sigma_le_prod_abFactor hN
  have hNpos : (0:ℚ) < (N:ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hab : (4:ℚ) * (N:ℚ) ≤ ((sigma 1 N : ℕ) : ℚ) := by exact_mod_cast habund
  nlinarith [hle, hlt, hNpos, hab]

/-! ## Parity of `σ`: `σ(n)` is odd exactly when the odd number `n` is a square -/

