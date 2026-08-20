/-!
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib` in
`RequestProject/Cassini11Mathlib.lean`). It is defined here so that this file,
which must begin with the header comment above, needs no `import` line. -/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 11`**: `F 10 * F 12 - F 11 ^ 2 = (-1) ^ 11`.

Numerically: `55 * 144 - 89 ^ 2 = 7920 - 7921 = -1`.

This is the `n = 11` instance of Cassini's identity, which is available in Mathlib as
`Int.fib_succ_mul_fib_pred_sub_fib_sq`; that derivation is carried out in
`RequestProject/Cassini11Mathlib.lean` as `Math.cassini_11_of_mathlib`. -/
