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

theorem solvable_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  exact solvable_of_nat_eq (by omega) (show 0 < k + 1 by omega)
    (show 0 < 2 * ((4 * k + 3) * (k + 1)) by positivity)
    (show 0 < 2 * ((4 * k + 3) * (k + 1)) by positivity) (by ring)

/-- `4 / n` is a sum of three unit fractions whenever `n ≡ 2 [MOD 3]`. -/
