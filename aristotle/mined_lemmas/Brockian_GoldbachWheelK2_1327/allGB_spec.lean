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

lemma allGB_spec : ∀ {K : ℕ}, allGB K = true → ∀ {k : ℕ}, k < K →
    gbFrom (2 * k + 4) 2 128 = true := by
  intro K
  induction K with
  | zero => intro _ k hk; omega
  | succ K ih =>
      intro h k hk
      rw [allGB, Bool.and_eq_true] at h
      rcases Nat.lt_or_ge k K with hlt | hge
      · exact ih h.2 hlt
      · have : k = K := by omega
        subst this
        exact h.1

/-! ## The wheel statement -/

/-- `m` is a **Goldbach K2 wheel modulus** when `m` is prime and the whole wheel window
`[4, 2 * m]` is covered by the binary (`K2`) Goldbach property: every even `n` in that
window is a sum of two primes. -/
