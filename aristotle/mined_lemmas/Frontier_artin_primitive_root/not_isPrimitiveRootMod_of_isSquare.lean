import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
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

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo the prime `p` when its residue generates the
multiplicative group `(ZMod p)ˣ`, i.e. when the multiplicative order of `a` in `ZMod p`
equals `p - 1`. -/

theorem not_isPrimitiveRootMod_of_isSquare {a : ℤ} (ha : IsSquare a) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ IsPrimitiveRootMod a p := by
  haveI := Fact.mk hp
  obtain ⟨b, rfl⟩ := ha
  intro h
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h' | h'
    · omega
    · exact h'
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hcast : ((b * b : ℤ) : ZMod p) = (b : ZMod p) * (b : ZMod p) := by push_cast; ring
  rw [IsPrimitiveRootMod, hcast] at h
  by_cases hx0 : (b : ZMod p) = 0
  · rw [hx0] at h
    have h1 : ((0 : ZMod p) * 0) ^ (p - 1) = 1 := by
      rw [← h]; exact pow_orderOf_eq_one _
    rw [zero_mul, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  · have hpow : ((b : ZMod p) * (b : ZMod p)) ^ ((p - 1) / 2) = 1 := by
      have h2 : ((b : ZMod p) * (b : ZMod p)) ^ ((p - 1) / 2)
          = (b : ZMod p) ^ (2 * ((p - 1) / 2)) := by
        rw [pow_mul]; ring_nf
      rw [h2]
      have : 2 * ((p - 1) / 2) = p - 1 := by omega
      rw [this]
      exact ZMod.pow_card_sub_one_eq_one hx0
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    rw [h] at hdvd
    have hle : p - 1 ≤ (p - 1) / 2 := Nat.le_of_dvd (by omega) hdvd
    omega

/-- If `a` is a perfect square then the only prime it can be a primitive root for is `2`;
in particular the set of such primes is finite. -/
