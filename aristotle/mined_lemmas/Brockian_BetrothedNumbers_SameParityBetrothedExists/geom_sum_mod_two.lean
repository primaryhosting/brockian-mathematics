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

theorem geom_sum_mod_two {p : ℕ} (hp : Odd p) (N : ℕ) :
    (∑ k ∈ Finset.range N, p ^ k) % 2 = N % 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hpk : p ^ N % 2 = 1 := Nat.odd_iff.mp (hp.pow)
      omega

/-- Key classical fact: if the sum of divisors of `n` is odd, then `n` is
either a square or twice a square. -/
