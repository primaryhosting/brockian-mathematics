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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ErdosStraus

/-- `ErdosStrausSolvable n` says that `4 / n` is a sum of three unit fractions with
positive natural denominators. -/

theorem solvable_of_even {n : ℕ} (hn : 0 < n) (h : n % 2 = 0) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  have hk : 0 < k := by omega
  exact solvable_of_nat_eq hn hk (show 0 < 2 * k by omega) (show 0 < 2 * k by omega) (by ring)

/-- `4 / n` is a sum of three unit fractions whenever `3 ∣ n`. -/
