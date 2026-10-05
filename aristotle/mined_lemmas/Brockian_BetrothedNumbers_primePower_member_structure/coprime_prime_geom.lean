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

namespace Brockian
namespace BetrothedNumbers

open Finset
open scoped ArithmeticFunction.sigma

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, they are distinct,
and the sum of the divisors of each, other than the number itself and `1`, gives the other;
equivalently `σ m = σ n = m + n + 1`. -/

lemma coprime_prime_geom {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Nat.Coprime p (∑ i ∈ range (k + 1), p ^ i) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp, geom_split]
  intro hdvd
  have : p ∣ 1 := (Nat.dvd_add_right (Dvd.intro _ rfl)).mp (by rwa [add_comm] at hdvd)
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp this)

