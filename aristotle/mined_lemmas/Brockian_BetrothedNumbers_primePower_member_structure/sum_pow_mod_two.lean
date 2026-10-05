/-
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction
/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive and distinct, and
the sum of the divisors of each, other than the number itself and `1`, is the other member;
equivalently `sigma m = sigma n = m + n + 1`. -/

theorem sum_pow_mod_two {p : ℕ} (hp : Odd p) (m : ℕ) :
    (∑ i ∈ Finset.range m, p ^ i) % 2 = m % 2 := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih]
      have : p ^ k % 2 = 1 := Nat.odd_iff.mp hp.pow
      omega

