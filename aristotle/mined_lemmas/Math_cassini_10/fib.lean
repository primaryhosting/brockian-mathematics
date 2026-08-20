/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.

This file is required to begin with the header comment above, which Lean only accepts as a
module docstring when the file has no `import` commands; hence the sequence is defined here
from scratch. The file `RequestProject/Cassini10Mathlib.lean` proves that this definition
agrees with Mathlib's `Nat.fib`, and derives the same identity for `Nat.fib` from Mathlib's
Cassini identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity** at `n = 10`: `F(9) * F(11) - F(10)^2 = (-1)^10`. -/
