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

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to come before any module docstring, so the header
-- above appears both at the very top of the file (as a plain comment) and here, after the
-- import, as the module docstring.

namespace Brockian.PolignacPrimes

/-- `GapOccursInfinitelyOften n` says that there are infinitely many pairs of *consecutive*
primes whose difference is exactly `n`: for every bound `N` there is a prime `p > N` such that
`p + n` is prime and no integer strictly between `p` and `p + n` is prime. -/

theorem gap_two_iff_twin_primes :
    GapOccursInfinitelyOften 2 ↔ PairsOccurInfinitelyOften 2 := by
  constructor
  · intro h N
    obtain ⟨p, hpN, hp, hp2, -⟩ := h N
    exact ⟨p, hpN, hp, hp2⟩
  · intro h N
    obtain ⟨p, hpN, hp, hp2⟩ := h (max N 2)
    refine ⟨p, lt_of_le_of_lt (le_max_left N 2) hpN, hp, hp2, ?_⟩
    intro c hc1 hc2 hcprime
    have hcp : c = p + 1 := by omega
    have hp2' : 2 < p := lt_of_le_of_lt (le_max_right N 2) hpN
    have hodd : ¬ (2 ∣ p) := by
      intro hd
      have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 hd)
      omega
    have : (2 : ℕ) ∣ c := by omega
    have := (Nat.Prime.eq_one_or_self_of_dvd hcprime 2 this)
    omega

/-- Unconditional reduction: if some `n > 0` occurs infinitely often as a difference of two
(not necessarily consecutive) primes, then some `0 < m ≤ n` occurs infinitely often as a gap
between consecutive primes. -/
