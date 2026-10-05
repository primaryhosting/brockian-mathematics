/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.

(Defined here rather than using `Nat.fib` because the required file header must be the very
first thing in the file, and Lean forbids any `import` after a comment at the start of a file.
This definition agrees with `Nat.fib` by construction.) -/

@[simp] theorem fib_three : fib 3 = 2 := rfl
