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

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- `Betrothed m n` says that `m` and `n` are a pair of *betrothed*
(quasi-amicable) numbers: two distinct positive integers each of whose sum of
divisors equals `m + n + 1`. -/

theorem sq_or_two_sq_of_betrothed_sameParity {m n : ℕ} (hB : Betrothed m n)
    (hpar : m % 2 = n % 2) :
    (∃ a, m = a ^ 2 ∨ m = 2 * a ^ 2) ∧ (∃ b, n = b ^ 2 ∨ n = 2 * b ^ 2) := by
  obtain ⟨hm, hn, _, hsm, hsn⟩ := hB
  have hoddm : Odd (∑ d ∈ m.divisors, d) := by rw [hsm, Nat.odd_iff]; omega
  have hoddn : Odd (∑ d ∈ n.divisors, d) := by rw [hsn, Nat.odd_iff]; omega
  exact ⟨exists_sq_of_odd_sigma hm.ne' hoddm, exists_sq_of_odd_sigma hn.ne' hoddn⟩

/-- **Conditional reduction for the Brockian "same parity betrothed" problem.**

It is a longstanding open question whether there exists a betrothed
(quasi-amicable) pair whose two members have the same parity; all known pairs
consist of one even and one odd number.

We prove the following unconditional structural reduction: *if* a same-parity
betrothed pair exists, then such a pair exists in which each member is either a
perfect square or twice a perfect square.  Indeed, for a same-parity pair the
common value `m + n + 1` of the two divisor sums is odd, and a number has odd
divisor sum exactly when it is a square or twice a square. -/
