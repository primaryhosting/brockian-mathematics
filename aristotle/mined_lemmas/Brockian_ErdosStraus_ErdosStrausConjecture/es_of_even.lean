import Brockian.ErdosStraus

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

/-- `ES n` says that `4 / n` is a sum of three positive unit fractions
(the Erdős–Straus property for `n`; the denominators need not be distinct). -/

theorem es_of_even {n : ℕ} (hn : n % 2 = 0) (hpos : 0 < n) : ES n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  exact es_mul es_two (by omega)

/-- Every `n ≡ 3 (mod 4)` has the Erdős–Straus property. -/
