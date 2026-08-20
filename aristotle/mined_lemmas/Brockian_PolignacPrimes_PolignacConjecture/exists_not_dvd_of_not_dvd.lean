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

theorem exists_not_dvd_of_not_dvd {r Q a n : ℕ} (hr : r.Prime) (hQ : ¬ r ∣ Q) (hn : Even n) :
    ∃ x : ℕ, ¬ (r ∣ a + Q * x) ∧ ¬ (r ∣ (a + n) + Q * x) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨v, hv0, hvn⟩ := exists_nonzero_shift_nonzero hr hn
  have hQ0 : (Q : ZMod r) ≠ 0 := fun h => hQ ((ZMod.natCast_eq_zero_iff _ _).mp h)
  set y : ZMod r := (v - (a : ZMod r)) * (Q : ZMod r)⁻¹ with hy
  have key : (a : ZMod r) + (Q : ZMod r) * y = v := by
    rw [hy]; field_simp; ring
  refine ⟨y.val, ?_, ?_⟩
  · intro h
    have h2 : ((a + Q * y.val : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    push_cast at h2
    rw [ZMod.natCast_val, ZMod.cast_id, key] at h2
    exact hv0 h2
  · intro h
    have h2 : ((a + n + Q * y.val : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    push_cast at h2
    rw [ZMod.natCast_val, ZMod.cast_id] at h2
    apply hvn
    rw [← key]
    linear_combination h2

/-- The Chinese-Remainder step: for every `n` there are `a` and `Q > 0` such that every
intermediate value `a + j` (`0 < j < n`) is divisible by some prime divisor of `Q`, while no
prime divisor of `Q` divides `a` or `a + n`.  (The primes used are the `n`-th, `(n+1)`-st, …
primes, all of which exceed `n`.) -/
