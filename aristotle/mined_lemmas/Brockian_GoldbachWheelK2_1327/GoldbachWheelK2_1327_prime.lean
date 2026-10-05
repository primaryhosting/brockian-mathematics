/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This module is deliberately import-free (Lean forbids `import` after the header
-- comment above), so primality is spelled out from first principles here.  The
-- companion module `RequestProject.GoldbachWheelK2_1327Mathlib` proves that
-- `Brockian.IsPrimeNat` coincides with Mathlib's `Nat.Prime`, and restates the
-- main theorem in Mathlib's vocabulary.

namespace Brockian

set_option maxRecDepth 100000

/-- Primality, from first principles: `n` is at least `2` and its only divisors are
`1` and `n`. -/

theorem GoldbachWheelK2_1327_prime :
    Nat.Prime 1327 ∧
    ∀ n : ℕ, 4 ≤ n → n ≤ 2 * 1327 → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ 103 ∧ p + q = n := by
  obtain ⟨h1327, hmain⟩ := GoldbachWheelK2_1327
  refine ⟨(isPrimeNat_iff_prime _).1 h1327, ?_⟩
  intro n h4 hle hev
  obtain ⟨p, q, hp, hq, hple, hsum⟩ := hmain n h4 hle (Nat.even_iff.1 hev)
  exact ⟨p, q, (isPrimeNat_iff_prime _).1 hp, (isPrimeNat_iff_prime _).1 hq, hple, hsum⟩

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

