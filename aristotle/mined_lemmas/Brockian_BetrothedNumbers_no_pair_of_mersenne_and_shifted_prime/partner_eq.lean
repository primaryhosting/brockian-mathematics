import Mathlib

/-!
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
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
open scoped ArithmeticFunction.sigma

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: both are positive and each has
divisor sum equal to `n + m + 1`.  (Distinctness of `n` and `m`, which is part of the usual
definition, is *not* assumed here; omitting it only makes the non-existence result stronger.) -/

lemma partner_eq {k p m : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (2 ^ k * p) m) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨-, -, hn, -⟩ := h
  rw [sigma_one_two_pow_mul_odd_prime hp hodd] at hn
  obtain ⟨b, hb⟩ : ∃ b : ℕ, 2 ^ k = b + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have hb2 : 2 ^ (k + 1) - 1 = 2 * b + 1 := by rw [pow_succ]; omega
  rw [hb2, hb] at hn
  rw [hb]
  simp only [Nat.add_sub_cancel]
  nlinarith [hn]

/-- **Main result.**  Let `k ≥ 2` and let `p` be an odd prime such that both the Mersenne
number `2 ^ k - 1` and the shifted prime `p + 2` are prime.  Then no natural number `m`
forms a betrothed pair with `2 ^ k * p`. -/
