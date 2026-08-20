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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-! ... -/`
-- because Lean 4 requires `import` commands to precede every other command, including
-- module docstrings.)

import Mathlib

/-!
# Polignac Conjecture

De Polignac's conjecture states that for every positive even number `n` there are infinitely
many pairs of *consecutive* primes `p < q` with `q - p = n`.  This is an open problem (the case
`n = 2` is the twin prime conjecture), so what is proved here is a *conditional reduction*:
Polignac's conjecture is derived from Dickson's conjecture on simultaneous primality of
linear forms.

The derivation is the classical one.  Given an even `n ≥ 2`, one chooses for each `j` with
`0 < j < n` a distinct prime `q j > n`, sets `Q = ∏ q j` and uses the Chinese Remainder Theorem
to find `a` with `q j ∣ a + j` for all such `j`.  The pair of linear forms `a + Q x`,
`(a + n) + Q x` is then admissible, so Dickson's conjecture produces arbitrarily large `x`
making both forms prime; and every intermediate value `a + Q x + j` (`0 < j < n`) is divisible
by the prime `q j`, which is smaller than it, hence composite.  So the two primes are
consecutive with difference exactly `n`.
-/

namespace Brockian
namespace PolignacPrimes

open Finset
open scoped Function

/-- `p` and `q` are consecutive primes: both are prime, `p < q`, and no prime lies strictly
between them. -/

theorem exists_nonzero_shift_nonzero {r n : ℕ} (hr : r.Prime) (hn : Even n) :
    ∃ v : ZMod r, v ≠ 0 ∧ v + (n : ZMod r) ≠ 0 := by
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases h0 : (n : ZMod r) = 0
  · exact ⟨1, one_ne_zero, by simp [h0]⟩
  · have hr2 : r ≠ 2 := by
      rintro rfl
      exact h0 (ZMod.natCast_eq_zero_iff_even.mpr hn)
    by_cases h1 : (1 : ZMod r) + (n : ZMod r) = 0
    · refine ⟨2, ?_, ?_⟩
      · intro h
        have h2 : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
        exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
          ((ZMod.natCast_eq_zero_iff _ _).mp h2))
      · have h3 : (2 : ZMod r) + (n : ZMod r) = ((1 : ZMod r) + n) + 1 := by ring
        rw [h3, h1, zero_add]
        exact one_ne_zero
    · exact ⟨1, one_ne_zero, h1⟩

/-- Admissibility at primes `r` not dividing the common difference `Q`. -/
