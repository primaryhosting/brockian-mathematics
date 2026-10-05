/-!
# Two Squares 41
Category: Pure Mathematics
Target: Math.two_squares_41
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime 41 is a sum of two squares.**

`41` is prime (it is at least `2` and its only divisors are `1` and `41`) and
`41 = 4 ^ 2 + 5 ^ 2`.

The fixed header comment above must be the first thing in this file, which makes an
`import` line illegal here, so primality is spelled out directly and the proof uses
only Lean's core library.  See `RequestProject/MathMathlib.lean` for the same fact
stated with Mathlib's `Nat.Prime` and derived from `Nat.Prime.sq_add_sq`. -/

theorem two_squares_41_prime : Nat.Prime 41 ∧ ∃ a b : ℕ, 41 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 4, 5, by norm_num⟩

/-- The same existence statement derived from Mathlib's Fermat two-squares theorem
`Nat.Prime.sq_add_sq`. -/
