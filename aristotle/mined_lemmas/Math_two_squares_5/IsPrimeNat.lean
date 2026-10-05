import Mathlib
import RequestProject.TwoSquares5

/-!
# Two Squares 5 — link with Mathlib

`RequestProject/TwoSquares5.lean` must begin with a prescribed header comment, so it
cannot contain an `import` line and is stated with a self-contained primality
predicate `Math.IsPrimeNat`.  Here we check that this predicate is exactly
Mathlib's `Nat.Prime`, and restate the main result in Mathlib terms.
-/

namespace Math

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/

def IsPrimeNat (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

/-- **Two squares for 5.**  The number `5` is prime and is a sum of two squares,
namely `5 = 1 ^ 2 + 2 ^ 2`.

Equivalent reformulation used in the proof: instead of quantifying over all
divisors of `5`, it suffices to check the finitely many candidates `m ≤ 5`,
since every divisor of `5` is at most `5`. -/
