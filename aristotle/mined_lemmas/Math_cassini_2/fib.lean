import Mathlib
import RequestProject.Cassini2

/-!
# Cassini 2, in terms of Mathlib's `Nat.fib`
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 2`: `F(1)·F(3) − F(2)² = (−1)²`. -/
