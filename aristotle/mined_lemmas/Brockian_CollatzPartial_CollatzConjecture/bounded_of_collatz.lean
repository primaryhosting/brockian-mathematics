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

theorem bounded_of_collatz (h : ∀ n : ℕ, 0 < n → ReachesOne n) :
    ∀ n : ℕ, 0 < n → ∃ B : ℕ, ∀ k : ℕ, collatz^[k] n ≤ B := by
  intro n hn
  obtain ⟨k, hk⟩ := h n hn
  -- after step `k` the orbit cycles through `1, 4, 2`, so it is bounded by
  -- the max of the finitely many first values and `4`
  refine ⟨max 4 ((Finset.range (k + 1)).sup fun j => collatz^[j] n), ?_⟩
  intro j
  by_cases hjk : j ≤ k
  · refine le_trans ?_ (le_max_right _ _)
    exact Finset.le_sup (f := fun j => collatz^[j] n) (Finset.mem_range.mpr (by omega))
  · replace hjk : k < j := by omega
    -- `j = k + r` with `r > 0`; the tail is the cycle `1 → 4 → 2 → 1`
    have hcyc : ∀ r : ℕ, collatz^[r] 1 ≤ 4 := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
        match r with
        | 0 => simp
        | 1 => simp
        | 2 => simp [Function.iterate_succ_apply]
        | (m + 3) =>
          have h3 : collatz^[3] 1 = 1 := by
            simp [Function.iterate_succ_apply]
          have : collatz^[m + 3] 1 = collatz^[m] (collatz^[3] 1) := by
            rw [← Function.iterate_add_apply]
          rw [this, h3]
          exact ih m (by omega)
    have hsplit : collatz^[j] n = collatz^[j - k] (collatz^[k] n) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [hsplit, hk]
    exact le_trans (hcyc (j - k)) (le_max_left _ _)

/-- Conversely, the Collatz conjecture implies the only positive periodic points are `1, 2, 4`. -/
