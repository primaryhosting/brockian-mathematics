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
-- (Lean 4 requires `import` to precede any module docstring, so the header above is a
-- plain comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n / 2` if `n` is even, `n ↦ 3 * n + 1` if `n` is odd. -/

lemma reachesOne_of_check : ∀ (f n : ℕ), reachesOneCheck f n = true → ReachesOne n := by
  intro f
  induction f with
  | zero =>
      intro n h
      simp [reachesOneCheck] at h
      exact ⟨0, by simp [h]⟩
  | succ f ih =>
      intro n h
      rw [reachesOneCheck] at h
      rcases Bool.or_eq_true_iff.mp h with h1 | h1
      · exact ⟨0, by simpa using (beq_iff_eq.mp h1)⟩
      · obtain ⟨k, hk⟩ := ih _ h1
        exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- Unconditional partial result: every `n` with `1 ≤ n ≤ 40` reaches `1`. -/
