import Mathlib
import RequestProject.Main

/-!
# Bridge to Mathlib's `Nat.fib`

`Math.fib` (defined in `RequestProject.Main` without imports, as required by the
file header there) agrees with Mathlib's `Nat.fib`, so `Math.cassini_8` is a
statement about the usual Fibonacci numbers.
-/

namespace Math

theorem fib_eq_natFib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 8`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_8_natFib :
    (Nat.fib 7 : ℤ) * (Nat.fib 9 : ℤ) - (Nat.fib 8 : ℤ) ^ 2 = (-1) ^ 8 := by
  simpa [fib_eq_natFib] using cassini_8

end Math

/-!
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, with `fib 0 = 0` and `fib 1 = 1`.
This agrees with `Nat.fib` from Mathlib; it is defined here because the
required header comment must be the very first item in the file, which
precludes an `import` command. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 8`: `F(7) * F(9) - F(8)^2 = (-1)^8`. -/
theorem cassini_8 :
    (fib 7 : Int) * (fib 9 : Int) - (fib 8 : Int) ^ 2 = (-1) ^ 8 := by
  decide

end Math

