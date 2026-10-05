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

/-
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BrocardGap

open Nat

/-- `BrocardFree n` says that `n ! + 1` is not a perfect square, i.e. `n` is not a
solution of Brocard's problem. -/

theorem even_of_gapTwo {n a : ℕ} (hn : 2 ≤ n) (ha : a * (a + 2) = n !) : Even a := by
  rcases Nat.even_or_odd a with h | h
  · exact h
  · exfalso
    have hodd : Odd (a * (a + 2)) := h.mul (by simpa using h.add_even (by decide))
    rw [ha] at hodd
    have hdvd : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
    rw [Nat.odd_iff] at hodd
    omega

/-- A modular certificate: if `n ! + 1` is not a quadratic residue mod `q`, then `n` is
Brocard-free. -/
