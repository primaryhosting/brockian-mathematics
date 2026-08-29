import Mathlib

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

/-
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The infinitude of amicable numbers is a well-known open problem.  What is proved here is a
*conditional reduction*: if Thabit ibn Qurra's rule produces amicable pairs for arbitrarily
large parameters (i.e. there are arbitrarily large `m` for which the three Thabit numbers
`3·2^m - 1`, `3·2^(m+1) - 1`, `9·2^(2m+1) - 1` are all prime), then there are infinitely many
amicable numbers.  The Thabit construction itself is proved unconditionally
(`Brockian.AmicableNumbers.isAmicablePair_thabit`), as is the classical example `(220, 284)`.
-/

namespace Brockian.AmicableNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- `a` and `b` form an amicable pair: they are distinct and each one's proper divisors sum to
the other, equivalently `σ a = σ b = a + b`. -/

theorem isAmicablePair_of_thabit_data {m B p q r : ℕ} (hB : 2 ^ m = B + 1) (hB1 : 1 ≤ B)
    (hp : p = 3 * B + 2) (hq : q = 6 * B + 5) (hr : r = 18 * B ^ 2 + 36 * B + 17)
    (hpp : p.Prime) (hqp : q.Prime) (hrp : r.Prime) :
    IsAmicablePair (2 ^ (m + 1) * (p * q)) (2 ^ (m + 1) * r) := by
  have h2 : 2 ^ (m + 1) = 2 * B + 2 := by rw [pow_succ]; omega
  have hS : σ 1 (2 ^ (m + 1)) = 4 * B + 3 := by
    have h := sigma_one_two_pow (m + 1)
    have h4 : 2 ^ (m + 1 + 1) = 4 * B + 4 := by
      rw [pow_succ, pow_succ]; omega
    omega
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hr2 : r ≠ 2 := by nlinarith [sq_nonneg B]
  have hpq : p ≠ q := by omega
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).2 hpq
  have hc1 : Nat.Coprime (2 ^ (m + 1)) (p * q) :=
    Nat.Coprime.mul_right (coprime_two_pow_of_odd_prime hpp hp2)
      (coprime_two_pow_of_odd_prime hqp hq2)
  have hc2 : Nat.Coprime (2 ^ (m + 1)) r := coprime_two_pow_of_odd_prime hrp hr2
  have hsa : σ 1 (2 ^ (m + 1) * (p * q)) = (4 * B + 3) * ((p + 1) * (q + 1)) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hc1, hS,
      isMultiplicative_sigma.map_mul_of_coprime hcpq, sigma_one_prime hpp,
      sigma_one_prime hqp]
  have hsb : σ 1 (2 ^ (m + 1) * r) = (4 * B + 3) * (r + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hc2, hS, sigma_one_prime hrp]
  refine ⟨?_, ?_, ?_⟩
  · have hlt : p * q < r := by subst hp hq hr; nlinarith
    have h2pos : 0 < 2 ^ (m + 1) := Nat.two_pow_pos _
    exact Nat.ne_of_lt (Nat.mul_lt_mul_of_pos_left hlt h2pos)
  · rw [hsa, h2]; subst hp hq hr; ring
  · rw [hsb, h2]; subst hp hq hr; ring

/-- Thabit ibn Qurra's rule in its usual form. -/
