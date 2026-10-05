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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian.SuperperfectNumbers

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

lemma four_dvd_sigma1_primePow {p e : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (he : Odd e) :
    4 ∣ sigma1 (p ^ e) := by
  rw [sigma1_primePow hp]
  have h : ((∑ i ∈ range (e + 1), p ^ i : ℕ) : ZMod 4) = 0 := by
    push_cast
    have hpc : ((p : ZMod 4)) = -1 := by
      have h4 := ZMod.natCast_mod p 4
      rw [hp4] at h4
      rw [← h4]; decide
    simp only [hpc, neg_one_geom_sum]
    simp [Nat.even_add_one, Nat.not_even_iff_odd.mpr he]
  exact (ZMod.natCast_eq_zero_iff _ _).mp h

/-! ### The key structural lemma -/

/-- If `σ(m) ≡ 2 (mod 4)` then `m` has a prime divisor congruent to `1` modulo `4`.

Indeed, `σ(m)` is the product of the numbers `σ(p^{v_p(m)})`; the factor at `p = 2` is odd,
a factor at an odd prime with even exponent is odd, and a factor at a prime `p ≡ 3 (mod 4)`
with odd exponent is divisible by `4`. So if no prime divisor of `m` were `≡ 1 (mod 4)`,
then `σ(m)` would be either odd or divisible by `4`. -/
