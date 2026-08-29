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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset

/-- The sum of the proper divisors of `n`. -/

theorem exists_amicable_of_thabitTriple {m : ℕ} (hm : 1 ≤ m) (h : ThabitTriple m) :
    IsAmicable (2 ^ (m + 1) * (9 * 2 ^ (2 * m + 1) - 1)) := by
  obtain ⟨hpp, hqp, hrp⟩ := h
  have h1 : (1:ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : (1:ℕ) ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  have h3 : (1:ℕ) ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  refine ⟨2 ^ (m + 1) * (3 * 2 ^ m - 1) * (3 * 2 ^ (m + 1) - 1), ?_⟩
  obtain ⟨hne, h₁, h₂⟩ := thabit_amicable (m := m) (p := 3 * 2 ^ m - 1)
    (q := 3 * 2 ^ (m + 1) - 1) (r := 9 * 2 ^ (2 * m + 1) - 1) hm (by omega) (by omega)
    (by omega) hpp hqp hrp
  exact ⟨hne.symm, h₂, h₁⟩

/-! ### The conditional infinitude statement -/

/-- **Conditional infinitude of amicable numbers.**  If Thâbit's triple condition holds for
infinitely many `m` (a classical open conjecture), then there are infinitely many amicable
numbers. -/
