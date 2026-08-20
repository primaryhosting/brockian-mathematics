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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)

import Mathlib

/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat

namespace Brockian.TwinPrimes

/-! ## The statement

The twin prime conjecture asserts that there are arbitrarily large primes `p` such that
`p + 2` is also prime.  This is a famous open problem, so it is not proved here; instead
we give an unconditional, Lean-checked *equivalent reformulation* (Clement's criterion,
derived from Wilson's theorem — `Nat.prime_iff_fac_equiv_neg_one` in Mathlib), which
turns the conjecture into a single divisibility statement about factorials, together with
some unconditional partial results.
-/

/-- `n` and `n + 2` are both prime. -/

theorem twinPrimeConjecture_iff_clement :
    TwinPrimeConjecture ↔
      ∀ N : ℕ, ∃ k : ℕ, N < k ∧
        (2 * k + 1) * (2 * k + 3) ∣ 4 * ((2 * k)! + 1) + (2 * k + 1) := by
  constructor
  · intro h N
    obtain ⟨p, hp, hpp⟩ := h (2 * N + 3)
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.1.odd_of_ne_two (by omega))
    obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
    refine ⟨k, by omega, ?_⟩
    rw [← clement k (by omega), ← hk]
    exact hpp
  · intro h N
    obtain ⟨k, hk, hdvd⟩ := h (N + 1)
    exact ⟨2 * k + 1, by omega, (clement k (by omega)).mpr hdvd⟩

/-! ## Unconditional partial results -/

/-- `(3, 5)` is a twin prime pair, so twin primes exist. -/
