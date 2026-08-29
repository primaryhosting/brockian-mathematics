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

theorem isAmicablePair_thabit {m : ℕ} (h : ThabitTriple m) :
    IsAmicablePair (2 ^ (m + 1) * ((3 * 2 ^ m - 1) * (3 * 2 ^ (m + 1) - 1)))
      (2 ^ (m + 1) * (9 * 2 ^ (2 * m + 1) - 1)) := by
  obtain ⟨hm, hp, hq, hr⟩ := h
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  set B := 2 ^ m - 1 with hBdef
  have hB : 2 ^ m = B + 1 := by omega
  have hB1 : 1 ≤ B := by omega
  have e1 : 3 * 2 ^ m - 1 = 3 * B + 2 := by omega
  have e2 : 3 * 2 ^ (m + 1) - 1 = 6 * B + 5 := by rw [pow_succ]; omega
  have e3 : 9 * 2 ^ (2 * m + 1) - 1 = 18 * B ^ 2 + 36 * B + 17 := by
    have h : 2 ^ (2 * m + 1) = 2 * (B + 1) ^ 2 := by
      rw [pow_succ, two_mul, pow_add, hB]; ring
    rw [h]
    have : 9 * (2 * (B + 1) ^ 2) = 18 * B ^ 2 + 36 * B + 18 := by ring
    omega
  exact isAmicablePair_of_thabit_data hB hB1 e1 e2 e3 hp hq hr

/-- The Thabit condition holds at `m = 1` (giving the pair `(220, 284)`). -/
