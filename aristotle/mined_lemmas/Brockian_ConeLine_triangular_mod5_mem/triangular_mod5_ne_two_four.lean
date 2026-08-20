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

import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- The `n`-th triangular number, computed in `ℕ` (division after multiplication). -/

theorem triangular_mod5_ne_two_four (n : ℕ) :
    ((T n : ℕ) : ZMod 5) ≠ 2 ∧ ((T n : ℕ) : ZMod 5) ≠ 4 := by
  have h := triangular_mod5_mem n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩

end Brockian.ConeLine

