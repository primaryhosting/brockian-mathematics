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

namespace Brockian

/-! ## A kernel-friendly primality test

Mathlib's `Decidable` instance for `Nat.Prime` performs a linear scan, which makes
`by decide` unusable for numbers of the size we need.  We therefore set up a trial
division test by divisors `≤ 63`, which is sound for all `n < 64 ^ 2 = 4096`.
-/

/-- `noSmallDiv n k = true` asserts that no `d` with `2 ≤ d ≤ k` and `d ≠ n` divides `n`. -/

lemma gbFrom_spec {n : ℕ} (hn : n < 4096) : ∀ {f p : ℕ}, gbFrom n p f = true →
    ∃ a b : ℕ, Nat.Prime a ∧ Nat.Prime b ∧ a + b = n := by
  intro f
  induction f with
  | zero => intro p h; simp [gbFrom] at h
  | succ f ih =>
      intro p h
      rw [gbFrom, Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hle, hp⟩, hq⟩ := h
        refine ⟨p, n - p, prime_of_isPrimeB (by omega) hp,
          prime_of_isPrimeB (by omega) hq, by omega⟩
      · exact ih h

/-- `allGB K = true` checks the Goldbach property for all even numbers `4, 6, …, 2K + 2`. -/
