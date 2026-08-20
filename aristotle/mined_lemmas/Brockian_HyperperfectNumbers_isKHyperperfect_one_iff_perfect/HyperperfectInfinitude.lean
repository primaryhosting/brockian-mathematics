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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect if `n = 1 + k * (σ n - n - 1)`, i.e. `n` is one plus `k` times the
sum of its proper divisors other than `1`.  The definition is stated in the subtraction-free
form `k * σ n + 1 = (k + 1) * n + k`. -/

theorem HyperperfectInfinitude {q : ℕ} (hq : q.Prime)
    (H : {t : ℕ | 2 ≤ t ∧ (q ^ t - q + 1).Prime}.Infinite) :
    {n : ℕ | IsHyperperfect n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨t, ⟨ht2, htp⟩, htN⟩ := H.exists_gt (N + 1)
  set p := q ^ t - q + 1 with hpdef
  have hqt : q ≤ q ^ t := Nat.le_self_pow (by omega) q
  have hpq : q ^ t + 1 = p + q := by omega
  have hmem : IsHyperperfect (q ^ (t - 1) * p) :=
    ⟨q - 1, isKHyperperfect_minoli hq htp ht2 hpq⟩
  have hbig : N < q ^ (t - 1) * p := by
    have h1 : t - 1 < 2 ^ (t - 1) := Nat.lt_two_pow_self
    have h2 : (2:ℕ) ^ (t - 1) ≤ q ^ (t - 1) := Nat.pow_le_pow_left hq.two_le _
    have h3 : 1 ≤ p := by have := htp.two_le; omega
    calc N < t - 1 := by omega
    _ < 2 ^ (t - 1) := h1
    _ ≤ q ^ (t - 1) := h2
    _ ≤ q ^ (t - 1) * p := Nat.le_mul_of_pos_right _ (by omega)
  exact absurd (hN hmem) (by omega)

/-- Sanity check that the definition is the standard one: `21 = 1 + 2 * (32 - 21 - 1)` is the
smallest `2`-hyperperfect number, obtained from Minoli's family with `q = 3`, `t = 2`, `p = 7`. -/
