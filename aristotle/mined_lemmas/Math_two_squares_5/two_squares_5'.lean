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

theorem two_squares_5' : Nat.Prime 5 ∧ ∃ a b : Nat, 5 = a ^ 2 + b ^ 2 :=
  ⟨(isPrimeNat_iff_prime 5).mp two_squares_5.1, two_squares_5.2⟩

end Math

/-!
# Two Squares 5
Category: Pure Mathematics
Target: Math.two_squares_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `IsPrimeNat n` says that `n` is a prime natural number: it is at least `2`,
and its only divisors are `1` and itself.  (This is stated self-containedly so
that this file can begin with the required header comment; the file
`TwoSquares5Mathlib.lean` proves that it agrees with Mathlib's `Nat.Prime`.) -/
