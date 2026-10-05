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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ## Betrothed (quasi-amicable) pairs -/

/-- A *betrothed* (quasi-amicable) pair: two positive integers each of whose sum of
divisors equals `m + n + 1`; equivalently `s(m) = n + 1` and `s(n) = m + 1`, where `s`
denotes the sum of the proper divisors. -/

theorem twentyOne_primeFactors_of_odd_of_four_mul_lt_sigma {N : ℕ} (hodd : Odd N)
    (h : 4 * N < σ 1 N) : 21 ≤ N.primeFactors.card := by
  by_contra hc
  push_neg at hc
  have hN : N ≠ 0 := by rintro rfl; simp at hodd
  have hNpos : (0 : ℚ) < (N : ℚ) := by
    have : 0 < N := Nat.pos_of_ne_zero hN
    exact_mod_cast this
  have hodds : ∀ p ∈ N.primeFactors, Nat.Prime p ∧ Odd p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    refine ⟨hprime, ?_⟩
    rcases hprime.eq_two_or_odd' with rfl | hodd'
    · exfalso
      have hdvd := Nat.dvd_of_mem_primeFactors hp
      rw [Nat.odd_iff] at hodd
      omega
    · exact hodd'
  have hprod := prod_lt_four_of_card_le_twenty hodds (by omega)
  have h1 : (4 * N : ℚ) < (σ 1 N : ℚ) := by exact_mod_cast h
  have h2 := sigma_one_le_prod_primeFactors hN
  have h3 : (N : ℚ) * ∏ p ∈ N.primeFactors, (p : ℚ) / ((p : ℚ) - 1) < (N : ℚ) * 4 :=
    mul_lt_mul_of_pos_left hprod hNpos
  linarith

/-! ## Main theorem -/

/-- **Hagis–Lord, Proposition 2 (second part).**  If `(m, n)` is a betrothed
(quasi-amicable) pair whose members are coprime and of the same parity, then both members
are odd and the product `m * n` has at least twenty-one distinct prime factors.

The argument: coprimality rules out both members being even, so both are odd.  Since
`m` and `n` are coprime, `σ₁(m * n) = σ₁(m) σ₁(n) = (m + n + 1)² > 4 m n`, so the odd
number `m * n` has abundancy index greater than `4`; by the rational abundancy bound its
Euler product `∏_{p ∣ mn} p / (p - 1)` exceeds `4`, which is impossible with twenty or
fewer odd prime factors, since the product over the first twenty odd primes is only
`3.9654...`. -/
