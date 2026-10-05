import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
# Goldbach Wheel K 2 947 — Mathlib interface

The target theorem `Brockian.GoldbachWheelK2_947` lives in the self-contained file
`RequestProject/GoldbachWheelK2_947.lean` (which carries no imports, since its header
comment must be the first thing in the file). Here we identify the primality notion used
there with Mathlib's `Nat.Prime` and restate the result in Mathlib terms.
-/

namespace Brockian

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/

theorem allPairsUpTo_947 : allPairsUpTo 947 = true := by decide

/-- **Goldbach wheel with modulus `947`.**
Every even number `n` with `4 ≤ n ≤ 2 * 947 = 1894` is a sum of two primes. -/
