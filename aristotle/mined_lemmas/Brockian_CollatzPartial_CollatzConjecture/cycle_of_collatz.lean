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

theorem cycle_of_collatz (h : ∀ n : ℕ, 0 < n → ReachesOne n) :
    ∀ m : ℕ, 0 < m → ∀ t : ℕ, 0 < t → collatz^[t] m = m → m = 1 ∨ m = 2 ∨ m = 4 := by
  intro m hm t ht hper
  obtain ⟨k, hk⟩ := h m hm
  -- `m` is periodic, hence it lies on the cycle through `1`
  have hiter : ∀ s : ℕ, collatz^[s * t] m = m := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
        have : (s + 1) * t = t + s * t := by ring
        rw [this, Function.iterate_add_apply, ih, hper]
  -- choose a multiple of `t` at least `k`, so that `m` equals an iterate of `1`
  have hmk : collatz^[k * t] m = m := hiter k
  have h1 : collatz^[k * t - k] (collatz^[k] m) = m := by
    rw [← Function.iterate_add_apply]
    have : k * t - k + k = k * t := by
      have : k ≤ k * t := Nat.le_mul_of_pos_right k ht
      omega
    rw [this, hmk]
  rw [hk] at h1
  -- iterates of `1` are `1, 4, 2` cyclically
  have hcyc : ∀ r : ℕ, collatz^[r] 1 = 1 ∨ collatz^[r] 1 = 4 ∨ collatz^[r] 1 = 2 := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      match r with
      | 0 => simp
      | 1 => simp
      | 2 => simp [Function.iterate_succ_apply]
      | (p + 3) =>
        have h3 : collatz^[3] 1 = 1 := by simp [Function.iterate_succ_apply]
        have : collatz^[p + 3] 1 = collatz^[p] (collatz^[3] 1) := by
          rw [← Function.iterate_add_apply]
        rw [this, h3]
        exact ih p (by omega)
  rcases hcyc (k * t - k) with hh | hh | hh <;> rw [hh] at h1
  · exact Or.inl h1.symm
  · exact Or.inr (Or.inr h1.symm)
  · exact Or.inr (Or.inl h1.symm)

end Brockian.CollatzPartial

