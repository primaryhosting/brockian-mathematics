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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, which Lean parses as a
command, so no `import` line may follow it.  The whole development below is therefore
self-contained and uses only the Lean 4 core library (no Mathlib).
-/

namespace Brockian.FortunateNumbers

/-! ## Primality and the primorial -/

/-- `IsPrime p` : `p` is a prime natural number. -/

theorem le_sq_of_index_le_ten {n m : Nat} (h2 : 2 ≤ n) (h10 : n ≤ 10) (h : IsFortunate n m) :
    m ≤ n * n := by
  have hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 := by omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [isFortunate_unique h isFortunate_two]; decide
  · rw [isFortunate_unique h isFortunate_three]; decide
  · rw [isFortunate_unique h isFortunate_four]; decide
  · rw [isFortunate_unique h isFortunate_five]; decide
  · rw [isFortunate_unique h isFortunate_six]; decide
  · rw [isFortunate_unique h isFortunate_seven]; decide
  · rw [isFortunate_unique h isFortunate_eight]; decide
  · rw [isFortunate_unique h isFortunate_nine]; decide
  · rw [isFortunate_unique h isFortunate_ten]; decide

/-- **Unconditional partial result.** Fortune's conjecture holds for all indices `n ≤ 10`. -/
