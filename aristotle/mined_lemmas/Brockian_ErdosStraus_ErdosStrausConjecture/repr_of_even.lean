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

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `ErdosStrausRepr n` says that `4/n` is a sum of three positive unit fractions. -/

theorem repr_of_even {n : ℕ} (hn : 0 < n) (h : n % 2 = 0) : ErdosStrausRepr n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  have hm : 0 < m := by omega
  refine ⟨m, 2 * m, 2 * m, hm, by omega, by omega, ?_⟩
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  push_cast
  field_simp
  ring

/-- Case `n ≡ 3 [MOD 4]`: `4/n = 1/(k+1) + 1/(2n(k+1)) + 1/(2n(k+1))` with `n = 4k+3`. -/
