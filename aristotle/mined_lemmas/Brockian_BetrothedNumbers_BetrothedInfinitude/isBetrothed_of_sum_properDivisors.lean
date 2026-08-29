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

-- (The header above is a plain block comment rather than a `/-!` module docstring only because
-- Lean 4 requires `import` commands to precede every command in a file, including docstrings.)

import Mathlib

/-!
# Betrothed Infinitude

## Betrothed (quasi-amicable) numbers

Two distinct positive integers `m ≠ n` are *betrothed* (or *quasi-amicable*) when each is the
sum of the proper divisors of the other, where "proper divisor" here excludes both `1` and the
number itself.  Equivalently

```
σ m = σ n = m + n + 1,
```

with `σ = ArithmeticFunction.sigma 1` the usual sum-of-divisors function.

Whether there are infinitely many betrothed pairs is an open problem, so the headline theorem
`BetrothedInfinitude` below is stated as a *conditional reduction*: from the (open) hypothesis
that betrothed numbers are unbounded we deduce that the set of betrothed pairs is infinite, and
`betrothed_infinite_iff_unbounded` shows that the two formulations are in fact equivalent.
Unconditionally we verify a list of explicit betrothed pairs.
-/

namespace Brockian.BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/
abbrev sigmaOne (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- `m` and `n` form a *betrothed pair*: they are distinct positive integers each of which is
the sum of the proper divisors of the other, where proper divisors exclude both `1` and the
number itself. -/

theorem isBetrothed_of_sum_properDivisors {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (h1 : ∑ d ∈ m.properDivisors, d = n + 1) (h2 : ∑ d ∈ n.properDivisors, d = m + 1) :
    IsBetrothed m n := by
  have hsm : sigmaOne m = ∑ d ∈ m.divisors, d := by
    simp [sigmaOne, ArithmeticFunction.sigma_apply]
  have hsn : sigmaOne n = ∑ d ∈ n.divisors, d := by
    simp [sigmaOne, ArithmeticFunction.sigma_apply]
  have em := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := m)
  have en := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := n)
  exact ⟨hm, hn, hmn, by omega, by omega⟩

/-! ### Explicit betrothed pairs -/

set_option maxRecDepth 8000000

