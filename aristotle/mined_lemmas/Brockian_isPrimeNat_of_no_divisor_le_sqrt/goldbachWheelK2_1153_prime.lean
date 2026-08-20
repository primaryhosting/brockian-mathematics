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

theorem goldbachWheelK2_1153_prime :
    Nat.Prime 1153 ∧
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * 1153 ∧
        Nat.Coprime p 1153 ∧ Nat.Coprime q 1153 := by
  obtain ⟨h1153, p, q, hp, hq, hsum, hpm, hqm⟩ := GoldbachWheelK2_1153
  have hP : Nat.Prime 1153 := isPrimeNat_iff_prime.mp h1153
  refine ⟨hP, p, q, isPrimeNat_iff_prime.mp hp, isPrimeNat_iff_prime.mp hq, hsum, ?_, ?_⟩
  · exact (Nat.Prime.coprime_iff_not_dvd hP).mpr
      (fun h => hpm (Nat.dvd_iff_mod_eq_zero.mp h)) |>.symm
  · exact (Nat.Prime.coprime_iff_not_dvd hP).mpr
      (fun h => hqm (Nat.dvd_iff_mod_eq_zero.mp h)) |>.symm

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

