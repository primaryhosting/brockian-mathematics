/-!
# Cassini 2
Category: Pure Mathematics
Target: Math.cassini_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to appear before any
other command, including a module docstring `/-! ... -/`.  Since this file must
*begin* with the header comment above, it cannot contain an `import Mathlib`
line.  We therefore give a self-contained development here (the Fibonacci
sequence is defined below), and additionally record the Mathlib-based version of
the same statement, phrased with `Nat.fib`, in `RequestProject/Main.lean`
(`Math.cassini_2_nat_fib`).
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/

lemma at this version, so we compute directly.) -/
