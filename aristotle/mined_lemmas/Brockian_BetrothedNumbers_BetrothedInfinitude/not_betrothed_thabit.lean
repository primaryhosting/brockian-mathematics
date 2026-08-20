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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any module docstring, so the header comment above is a
plain block comment and is repeated here as the module docstring.)
-/

open ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- Two positive integers `m ≠ n` are *betrothed* (a quasi-amicable pair) when the sum of the
divisors of each equals `m + n + 1`; equivalently, the sum of the divisors of each strictly
between `1` and the number itself equals the other number. -/

theorem not_betrothed_thabit {A p q r : ℕ} (hr : r.Prime) (hpodd : Odd p) (hqodd : Odd q)
    (hrodd : Odd r) (hAr : Nat.Coprime A r) : ¬ Betrothed (A * p * q) (A * r) := by
  intro h
  -- both members have the parity of `A`, so their sum is even and the divisor sums are odd
  have hpar : Even (A * p * q + A * r) := by
    have hsum : A * p * q + A * r = A * (p * q + r) := by ring
    rw [hsum]
    exact ((hpodd.mul hqodd).add_odd hrodd).mul_left A
  -- but `r` divides `A * r` exactly once, forcing the divisor sum to be even
  refine not_odd_prime_exactly_once h hpar hr hrodd ⟨A, Nat.mul_comm A r⟩ (fun hsq => ?_)
  have hrA : r ∣ A := by
    have : r * r ∣ r * A := by
      rw [← sq, Nat.mul_comm r A]; exact hsq
    exact (mul_dvd_mul_iff_left hr.pos.ne').1 this
  have hr1 : r ∣ 1 := hAr ▸ Nat.dvd_gcd hrA dvd_rfl
  exact hr.one_lt.ne' (Nat.eq_one_of_dvd_one hr1)

/-! ## The conditional infinitude theorem -/

/-- The hypothesis: there are arbitrarily large sigma splits. -/
