import Mathlib
/-!
# D Ocagne
Category: Fibonacci
Target: Fibonacci.dOcagne
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module docstrings, so the required header comment appears immediately after the import.

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

namespace Fibonacci

/-- **d'Ocagne's identity**, stated in addition form to avoid natural subtraction:
`F (m + n + 1) = F (m+1) * F (n+1) + F m * F n`, over the integers.
This is `Nat.fib_add` from Mathlib, cast to `ℤ`. -/

theorem dOcagne_signed_shift (n k : ℕ) :
    (Nat.fib (n + k) : ℤ) * (Nat.fib (n + 1) : ℤ)
      - (Nat.fib (n + k + 1) : ℤ) * (Nat.fib n : ℤ) = (-1) ^ n * (Nat.fib k : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := by
        simpa [Nat.add_comm] using (Nat.fib_add_two (n := n))
      have h2 : Nat.fib (n + k + 2) = Nat.fib (n + k) + Nat.fib (n + k + 1) := by
        simpa [Nat.add_comm] using (Nat.fib_add_two (n := n + k))
      have e1 : n + 1 + k = n + k + 1 := by omega
      have e2 : n + k + 1 + 1 = n + k + 2 := by omega
      have e3 : n + 1 + 1 = n + 2 := by omega
      rw [e1, e2, e3, h1, h2]
      push_cast
      push_cast at ih
      ring_nf
      ring_nf at ih
      linarith [ih]

/-- **d'Ocagne's identity** in signed form, for `n ≤ m`:
`F m * F (n+1) - F (m+1) * F n = (-1)^n * F (m - n)`. -/
