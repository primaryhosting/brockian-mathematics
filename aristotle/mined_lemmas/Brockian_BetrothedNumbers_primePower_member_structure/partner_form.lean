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

lemma partner_form {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    ∃ k : ℕ, a = k + 2 ∧ n = p * ∑ i ∈ range (k + 1), p ^ i := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  match a with
  | 0 => simp at h1
  | 1 =>
      rw [sigma_prime_pow hp 1] at h1
      simp [Finset.sum_range_succ, pow_one] at h1
      omega
  | (k + 2) =>
      refine ⟨k, rfl, ?_⟩
      rw [sigma_prime_pow hp (k + 2), Finset.sum_range_succ, geom_split] at h1
      omega

/-- The key numerical obstruction in the case `p = 2`. -/
