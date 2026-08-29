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
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The full Collatz conjecture is open.  What is proved here is:

* `CollatzConjecture` : a Lean-checked *conditional reduction* — if every integer `> 1`
  eventually iterates to a strictly smaller value (the descent property), then every
  positive integer reaches `1`.
* unconditional partial results: the descent property holds for every `n > 1` outside the
  residue class `3 (mod 4)`, and every power of two reaches `1`.
-/

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n/2` if `n` is even, `n ↦ 3n+1` if `n` is odd. -/

lemma reaches1_of_reaches1B : ∀ (f n : ℕ), reaches1B f n = true → Reaches1 n := by
  intro f
  induction f with
  | zero =>
      intro n h
      rw [reaches1B, beq_iff_eq] at h
      exact ⟨0, by simp [h]⟩
  | succ f ih =>
      intro n h
      rw [reaches1B, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · exact ⟨0, by simp [h]⟩
      · obtain ⟨k, hk⟩ := ih _ h
        exact ⟨k + 1, by rw [Function.iterate_add_apply]; simpa using hk⟩

set_option maxRecDepth 1000000 in
/-- Kernel-checked verification of the Collatz conjecture for all `1 ≤ n ≤ 1000`. -/
