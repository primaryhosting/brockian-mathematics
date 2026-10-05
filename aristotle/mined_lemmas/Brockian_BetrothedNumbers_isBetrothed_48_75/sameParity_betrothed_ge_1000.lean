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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- `IsBetrothed m n` says that `(m, n)` is a *betrothed* (quasi-amicable) pair:
two distinct positive integers each of whose sum of *proper* divisors is one more
than the other, i.e. `σ m = σ n = m + n + 1`. -/

theorem sameParity_betrothed_ge_1000 {m n : ℕ} (h : IsBetrothed m n) (hpar : m % 2 = n % 2) :
    1000 ≤ m ∧ 1000 ≤ n := by
  have main : ∀ a b : ℕ, IsBetrothed a b → a % 2 = b % 2 → 1000 ≤ a := by
    intro a b hb hp
    by_contra hlt
    push_neg at hlt
    obtain ⟨ha, hb0, hne, hsa, hsb⟩ := hb
    have hbv : b = sigma 1 a - a - 1 := by omega
    subst hbv
    exact betrothed_check_below_1000 a (Finset.mem_range.mpr hlt)
      ⟨ha, hne, by omega, by omega, hp⟩
  exact ⟨main m n h hpar, main n m (isBetrothed_symm h) hpar.symm⟩

/-- **Same-parity betrothed pairs, reduced.**

Whether a betrothed (quasi-amicable) pair of equal parity exists is an open problem.
This theorem gives a Lean-checked equivalent reformulation: such a pair exists if and
only if there is a betrothed pair both of whose members is a perfect square or twice
a perfect square.  (The underlying reason is `odd_sigma_iff`: for a betrothed pair the
common value `σ m = σ n = m + n + 1` is odd exactly when `m` and `n` have equal parity.)
See `sameParity_betrothed_ge_1000` for an unconditional partial result. -/
