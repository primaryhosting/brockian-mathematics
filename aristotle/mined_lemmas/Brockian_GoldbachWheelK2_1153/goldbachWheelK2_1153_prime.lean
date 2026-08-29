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

theorem goldbachWheelK2_1153_prime :
    Nat.Prime 1153 ∧
      ∀ n : ℕ, 4 ≤ n → n < 1153 → Even n →
        ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨h1153, hgold⟩ := GoldbachWheelK2_1153
  refine ⟨(isPrimeNat_iff_prime 1153).mp h1153, ?_⟩
  intro n h4 hlt hev
  obtain ⟨p, q, hp, hq, hsum⟩ := hgold n h4 hlt (Nat.even_iff.mp hev)
  exact ⟨p, q, (isPrimeNat_iff_prime p).mp hp, (isPrimeNat_iff_prime q).mp hq, hsum⟩

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

