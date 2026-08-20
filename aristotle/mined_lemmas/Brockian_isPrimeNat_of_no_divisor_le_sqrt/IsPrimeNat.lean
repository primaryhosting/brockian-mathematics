/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module doc comment, and Lean 4 forbids any
`import` after it, so this file is written in pure core Lean (no Mathlib) and is fully
self-contained.  The file `RequestProject/GoldbachWheelK2_1153Mathlib.lean` imports Mathlib and
this file, proves `Brockian.IsPrimeNat n ↔ Nat.Prime n`, and restates the result in Mathlib
vocabulary.
-/

namespace Brockian

/-- A natural number is prime when it is at least `2` and its only divisors are `1` and itself. -/

def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

/-- Trial-division criterion: a number `n ≥ 2` with no divisor `m` satisfying `m * m ≤ n`
(other than `1`) is prime. -/
