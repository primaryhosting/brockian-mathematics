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
