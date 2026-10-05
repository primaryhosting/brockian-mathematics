/-!
# Two Squares 37
Category: Pure Mathematics
Target: Math.two_squares_37
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: the required header above is a module docstring, and Lean does not
allow `import` commands after it, so this file is deliberately self-contained and uses no
imports.  Primality of `37` is therefore spelled out directly (`37 ≥ 2` and every divisor
of `37` is `1` or `37`) instead of via `Nat.Prime`.
-/

namespace Math

/-- `IsPrimeNat n` says that `n` is a prime natural number: it is at least `2` and its only
divisors are `1` and itself.  This is the standard definition, spelled out here because the
file has no imports. -/

def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

/-- `37` is prime. -/
