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
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean forbids `import` commands after a module docstring. So, in order for the
-- required header above to be the very first thing in the file, this development is
-- written to be self-contained: it uses only the Lean core prelude, with no `import`.

namespace Brockian.CollatzPartial

/-- The Collatz step: `n ↦ n / 2` for even `n`, and `n ↦ 3 * n + 1` for odd `n`. -/

theorem reaches1_of_reach1B : ∀ (fuel n : Nat), reach1B fuel n = true → Reaches1 n := by
  intro fuel
  induction fuel with
  | zero =>
      intro n h
      have : n = 1 := by simpa [reach1B] using h
      exact ⟨0, by simp [this]⟩
  | succ fuel ih =>
      intro n h
      rw [reach1B, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · exact ⟨0, by simp [h]⟩
      · obtain ⟨k, hk⟩ := ih (collatz n) h
        exact ⟨k + 1, by rw [collatzIter_succ']; exact hk⟩

/-- **Unconditional numerical verification.** Every `n` with `0 < n < 1000`
reaches `1`. -/
