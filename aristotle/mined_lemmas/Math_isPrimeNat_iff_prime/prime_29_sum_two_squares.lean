import Mathlib
import RequestProject.TwoSquares29

/-!
Mathlib-facing restatement of `Math.two_squares_29`: the predicate `Math.IsPrimeNat` used in
`RequestProject/TwoSquares29.lean` agrees with Mathlib's `Nat.Prime`, so `29` is a Mathlib-prime
which is a sum of two squares.
-/

namespace Math


theorem prime_29_sum_two_squares : Nat.Prime 29 ∧ ∃ a b : ℕ, 29 = a ^ 2 + b ^ 2 :=
  ⟨isPrimeNat_iff_prime.mp isPrimeNat_29, two_squares_29.2⟩

end Math

/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: the required header above is a module docstring, and Lean 4 does not
allow `import` commands after any command (including a module docstring).  To keep the header
exactly as requested at the very beginning of the file, this development is written without
imports, using only Lean core.  Primality is therefore spelled out explicitly below via
`Math.IsPrimeNat`, which is the standard definition of a prime natural number.
-/

namespace Math

/-- A natural number is prime when it is at least `2` and its only divisors are `1` and itself. -/
