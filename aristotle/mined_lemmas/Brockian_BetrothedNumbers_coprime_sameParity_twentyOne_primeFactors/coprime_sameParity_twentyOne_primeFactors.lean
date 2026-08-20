/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Finset
open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-!
## Betrothed (quasi-amicable) pairs

A pair `(m, n)` of positive integers is *betrothed* (also called *quasi-amicable*, or a
*reduced amicable pair*) when each of the two numbers is the sum of the *nontrivial* proper
divisors of the other, i.e. `σ₁ m = σ₁ n = m + n + 1`.
-/

/-- `Betrothed m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
the sum of divisors of each of `m` and `n` equals `m + n + 1`. -/

theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ} (hb : Betrothed m n)
    (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    Odd m ∧ Odd n ∧ IsSquare m ∧ IsSquare n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn⟩ := hb
  -- both members are nonzero
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp only [ArithmeticFunction.map_zero] at hm
    omega
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [ArithmeticFunction.map_zero] at hn
    omega
  -- coprimality plus equal parity forces both to be odd
  have hmodd : m % 2 = 1 := by
    by_contra hcon
    have hm2 : 2 ∣ m := by omega
    have hn2 : 2 ∣ n := by omega
    have : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd hm2 hn2
    rw [hcop] at this
    omega
  have hnodd : n % 2 = 1 := by omega
  have hmO : Odd m := Nat.odd_iff.mpr hmodd
  have hnO : Odd n := Nat.odd_iff.mpr hnodd
  -- `m + n + 1` is odd, so both members are perfect squares
  have hsum_odd : Odd (m + n + 1) := by
    rw [Nat.odd_iff]; omega
  have hsqm : IsSquare m := (odd_sigma_one_iff hm0 hmO).mp (hm ▸ hsum_odd)
  have hsqn : IsSquare n := (odd_sigma_one_iff hn0 hnO).mp (hn ▸ hsum_odd)
  refine ⟨hmO, hnO, hsqm, hsqn, ?_⟩
  -- the abundancy index of `m * n` exceeds `4`
  set N := m * n with hNdef
  have hN0 : N ≠ 0 := Nat.mul_ne_zero hm0 hn0
  have hNodd : Odd N := hmO.mul hnO
  have hsigmaN : σ 1 N = (m + n + 1) ^ 2 := by
    rw [hNdef, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hm, hn, sq]
  have hNpos : (0 : ℚ) < (N : ℚ) := by positivity
  have habund : 4 < (σ 1 N : ℚ) / N := by
    rw [lt_div_iff₀ hNpos, hsigmaN]
    have hmq : (0 : ℚ) < (m : ℚ) := by positivity
    have hnq : (0 : ℚ) < (n : ℚ) := by positivity
    have hNq : (N : ℚ) = (m : ℚ) * (n : ℚ) := by rw [hNdef]; push_cast; ring
    rw [hNq]
    push_cast
    nlinarith [sq_nonneg ((m : ℚ) - (n : ℚ))]
  exact twentyOne_primeFactors_of_abundancy_gt_four hN0 hNodd habund

/-!
## Historical computational lower bounds (not formalized)

The theorem above is the *exact* statement proved by Hagis and Lord (1977): a coprime
betrothed pair whose two members have the same parity consists of two odd squares whose
product has at least twenty-one distinct prime factors.

Separately from this exact result, the literature records purely *computational* facts about
betrothed numbers — for instance exhaustive searches showing that no betrothed pair of equal
parity occurs below various search bounds. Such statements depend on large finite computations
and are **not** formalized here; nothing in this file assumes them, and the theorem above is
proved unconditionally.
-/

end BetrothedNumbers
end Brockian

