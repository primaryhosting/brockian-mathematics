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

theorem GoldbachWheelK2_1153 :
    IsPrimeNat 1153 ∧
      ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = 2 * 1153 ∧
        p % 1153 ≠ 0 ∧ q % 1153 ≠ 0 :=
  ⟨isPrimeNat_1153, 13, 2293, isPrimeNat_13, isPrimeNat_2293, by decide, by decide, by decide⟩

end Brockian

import Mathlib
import RequestProject.GoldbachWheelK2_1153

/-!
# Goldbach Wheel K 2 1153 — Mathlib restatement

`RequestProject/GoldbachWheelK2_1153.lean` must be import-free (its mandated header is a module
doc comment, after which Lean forbids `import`), so it uses its own primality predicate
`Brockian.IsPrimeNat`.  Here we identify that predicate with Mathlib's `Nat.Prime` and restate
the Goldbach wheel result in Mathlib vocabulary.
-/

namespace Brockian

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/
