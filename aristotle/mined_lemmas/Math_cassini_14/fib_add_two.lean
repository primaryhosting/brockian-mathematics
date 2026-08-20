/-
Supplement to `RequestProject/Cassini14.lean`: identifies the Fibonacci sequence
`Math.fib` used there with Mathlib's `Nat.fib`, and restates Cassini 14 for `Nat.fib`.
-/
import Mathlib
import RequestProject.Cassini14

namespace Math


theorem fib_add_two (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

/-- Key intermediate lemma (Cassini's identity in product form):
`F (n + 1) * F (n + 3) - F (n + 2) * F (n + 2) = (-1) ^ (n + 2)` for every `n`. -/
