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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat
open ArithmeticFunction

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ n - n - 1)`.  Written without truncated
subtraction this reads `k * σ n + 1 = (k + 1) * n + k`.  For `k = 1` this is exactly
the condition that `n` is a perfect number. -/

theorem hyperperfect_of_witness {k p a q : ℕ} (h : Witness k p a q) :
    Hyperperfect k (p ^ a * q) := by
  obtain ⟨hp, hq, hne, ha, heq⟩ := h
  refine ⟨?_, ?_⟩
  · have h2 : 2 ≤ p ^ a := by
      calc 2 = 2 ^ 1 := rfl
      _ ≤ p ^ 1 := Nat.pow_le_pow_left hp.two_le 1
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
    have := hq.two_le
    nlinarith
  · rw [sigma_one_prime_pow_mul_prime hp hq hne]
    exact heq

/-- **The semiprime case.**  If `a * b = k ^ 2 + 1` and `k + a`, `k + b` are distinct primes,
then `(k + a) * (k + b)` is `k`-hyperperfect.  (Equivalently: for distinct primes `p, q`,
the number `p * q` is `k`-hyperperfect iff `(p - k) * (q - k) = k ^ 2 + 1`.) -/
