/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained and uses no imports, so that the header
comment above can be the very first thing in the file: Lean requires `import`
commands to precede every other command, including module documentation.
Consequently primality is developed from scratch here, as `Brockian.IsPrimeNat`.
The companion file `RequestProject/GoldbachWheelK2_1153Mathlib.lean` imports
Mathlib, proves `IsPrimeNat n ↔ Nat.Prime n`, and restates the main result in
Mathlib's vocabulary.
-/

namespace Brockian

/-- `IsPrimeNat n` is the usual definition of primality for natural numbers:
`n` is at least `2` and its only divisors are `1` and `n`. -/

def gwWheelCheck (s : Nat) : List (Nat × Nat) → Nat → Bool
  | [], _ => true
  | (p, q) :: ps, n =>
      (p + q == n) && primeBWith p s && primeBWith q s && gwWheelCheck s ps (n + 2)

