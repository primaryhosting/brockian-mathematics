/-!
# Quadruplet 11 13 17 19
Category: Frontier — Prime Numbers
Target: Constellation.quadruplet_11_13_17_19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Constellation

/-- Primality of a natural number, spelled out elementarily: `n` is at least `2`
and every divisor of `n` is either `1` or `n`.

This is stated without any `import` because Lean requires every `import` command to
precede all other syntax in a file, including the module docstring above; the file
`RequestProject/Quadruplet11131719Mathlib.lean` proves that `IsPrimeNat` is equivalent
to Mathlib's `Nat.Prime`, and restates the theorem below in those terms. -/

def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

