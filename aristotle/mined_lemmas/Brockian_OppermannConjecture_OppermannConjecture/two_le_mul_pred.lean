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

/-!
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.OppermannConjecture

/-- Primality of a natural number, stated from first principles (this file is self-contained
and imports nothing beyond Lean's prelude, so that the header comment above can literally be
the first thing in the file). -/

theorem two_le_mul_pred {n : Nat} (hn : 2 ≤ n) : 2 ≤ n * (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
  have h1 : 1 ≤ k := by omega
  have h2 : 1 * 1 ≤ k * k := Nat.mul_le_mul h1 h1
  omega

/-- The arithmetic identity `n * (n - 1) + n = n * n` for `n ≥ 1`. -/
