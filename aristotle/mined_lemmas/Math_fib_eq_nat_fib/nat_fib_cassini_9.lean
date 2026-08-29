import Mathlib
import RequestProject.Math

/-!
# Cassini's identity: companion file

`RequestProject.Math` is required to begin with a fixed header comment, hence it cannot
contain an `import` command and its Fibonacci sequence `Math.fib` is defined from scratch.
Here we import Mathlib and check that `Math.fib` is Mathlib's `Nat.fib`, restate
`Math.cassini_9` in terms of `Nat.fib`, and prove the general Cassini identity.

A search of this Mathlib version turned up no lemma stating Cassini's identity for
`Nat.fib` (only related identities such as `Nat.fib_add_two_sub_fib_add_one` and
`Nat.fib_two_mul_add_one`), so the general statement is proved here by induction.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem nat_fib_cassini_9 :
    (Nat.fib 8 : ℤ) * (Nat.fib 10 : ℤ) - (Nat.fib 9 : ℤ) ^ 2 = (-1) ^ 9 :=
  nat_fib_cassini 8

/-- The target statement `Math.cassini_9` is exactly Cassini's identity at `n = 8`
for Mathlib's Fibonacci sequence. -/
example :
    (Math.fib 8 : ℤ) * (Math.fib 10 : ℤ) - (Math.fib 9 : ℤ) ^ 2 = (-1) ^ 9 := by
  simp only [fib_eq_nat_fib]
  exact nat_fib_cassini_9

end Math

#print axioms Math.cassini_9
#print axioms Math.nat_fib_cassini
#print axioms Math.cassini

/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file must begin with the mandated header comment, so it cannot contain an
`import` line; `Math.fib` is therefore defined here from scratch.  It agrees with
Mathlib's `Nat.fib`, as proved by `Math.fib_eq_nat_fib` in `RequestProject.MathCassini`.) -/
