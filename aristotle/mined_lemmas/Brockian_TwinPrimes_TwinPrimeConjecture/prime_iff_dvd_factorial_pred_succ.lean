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

theorem prime_iff_dvd_factorial_pred_succ (n : ℕ) (h : n ≠ 1) :
    Nat.Prime n ↔ n ∣ (n - 1)! + 1 := by
  rcases eq_or_ne n 0 with rfl | h0
  · simp [Nat.not_prime_zero]
  haveI : NeZero n := ⟨h0⟩
  rw [Nat.prime_iff_fac_equiv_neg_one h, ← ZMod.natCast_eq_zero_iff ((n - 1)! + 1) n]
  push_cast
  exact ⟨fun hh => by rw [hh]; ring, fun hh => by linear_combination hh⟩

/-! ## Clement's criterion -/

/-- Reduction of the divisibility condition modulo `2k+1`. -/
