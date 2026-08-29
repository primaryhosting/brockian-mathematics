/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
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

namespace Brockian

/-- A trial-division primality test, valid for `n ≤ 727` (since `27 * 27 = 729 > 727`,
it suffices to rule out divisors `d` with `2 ≤ d < 27`). -/

theorem GoldbachWheelK2_727 :
    ∀ n : ℕ, 4 ≤ n → n ≤ 727 → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  have key : (List.range 728).all
      (fun n => !(decide (4 ≤ n) && decide (n % 2 = 0)) || wheelGoldbachTest n) = true := by
    decide
  rw [List.all_eq_true] at key
  intro n h4 h727 hev
  have hmem : n ∈ List.range 728 := List.mem_range.mpr (by omega)
  have h := key n hmem
  have hpar : n % 2 = 0 := Nat.even_iff.mp hev
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq,
    decide_eq_false_iff_not, hpar, h4, not_true_eq_false, false_and, false_or] at h
  exact wheelGoldbachTest_sound h727 h

end Brockian

