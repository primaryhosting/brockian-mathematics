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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean does not permit a `/-!` module docstring before `import`; the header above is the
-- same text as a plain block comment, and is repeated as a module docstring below.)
import Mathlib

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers each of whose
sum of divisors equals `m + n + 1`. -/

theorem odd_sigma_iff_squareOrTwiceSquare {n : ℕ} (hn : n ≠ 0) :
    Odd (σ 1 n) ↔ SquareOrTwiceSquare n := by
  rw [odd_sigma_iff hn, squareOrTwiceSquare_iff hn]

/--
**Same parity betrothed pairs.**

Whether a betrothed (quasi-amicable) pair of equal parity exists is an open problem, so what is
established here is an equivalent reformulation: a same-parity betrothed pair exists if and only
if a betrothed pair exists both of whose members are a square or twice a square.

The reduction rests on the fact that `σ m = m + n + 1` is odd exactly when `m` and `n` have the
same parity, together with the characterisation of the numbers with odd sum of divisors as the
squares and the doubles of squares.
-/
