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

theorem solvable_of_mod_eight_eq_five {n : ℕ} (h : n % 8 = 5) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 5 := ⟨n / 8, by omega⟩
  exact solvable_of_nat_eq (by omega) (show 0 < 2 * k + 2 by omega)
    (show 0 < (8 * k + 5) * (2 * k + 2) by positivity)
    (show 0 < (8 * k + 5) * (k + 1) by positivity) (by ring)

/-- **Main unconditional result.** The Erdős–Straus conjecture holds for every `n ≥ 2` whose
residue modulo `24` is different from `1`. -/
