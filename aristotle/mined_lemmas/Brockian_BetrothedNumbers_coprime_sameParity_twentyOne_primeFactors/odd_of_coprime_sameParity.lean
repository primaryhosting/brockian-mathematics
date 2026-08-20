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
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- Notation for the sum-of-divisors function `σ₁`. -/
local notation "σ₁" => ArithmeticFunction.sigma 1

/-! ## Definition -/

/-- A *betrothed* (or *quasi-amicable*) pair: two positive integers each of whose
sum of divisors equals the sum of the two numbers plus one. -/

lemma odd_of_coprime_sameParity {m n : ℕ} (hcop : Nat.Coprime m n) (hpar : Even m ↔ Even n) :
    Odd m ∧ Odd n := by
  have hm : ¬ Even m := by
    intro hm
    have hn : Even n := hpar.mp hm
    have h2m : 2 ∣ m := hm.two_dvd
    have h2n : 2 ∣ n := hn.two_dvd
    have : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd h2m h2n
    rw [hcop] at this
    omega
  have hn : ¬ Even n := fun hn => hm (hpar.mpr hn)
  exact ⟨Nat.odd_iff.mpr (Nat.not_even_iff.mp hm), Nat.odd_iff.mpr (Nat.not_even_iff.mp hn)⟩

/-- The product of a coprime betrothed pair has abundancy index exceeding `4`:
`σ₁ (m * n) = (m + n + 1) ^ 2 > (m + n) ^ 2 ≥ 4 m n`. -/
