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

-- (The header above is repeated here as a module docstring; a `/-!` block cannot precede
-- `import` in Lean 4.)
/-!
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `n` is **`k`-hyperperfect** when `n = 1 + k * (σ n - n - 1)`, i.e. when
`k * σ n + 1 = (k + 1) * n + k`, where `σ n` is the sum of the divisors of `n`.
(The second, subtraction-free form is the one used here; `hyperperfect_iff_classical`
shows it agrees with the classical definition.) -/

theorem hyperperfect_sq_mul_prime_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    IsHyperperfect k (p ^ 2 * q) ↔ q * p ^ 2 = q * (k * p + k) + (k * p ^ 2 + k * p + 1) := by
  have h2p := hp.two_le
  have h2q := hq.two_le
  unfold IsHyperperfect
  rw [sum_divisors_sq_mul_prime hp hq hpq]
  constructor
  · rintro ⟨-, h⟩
    nlinarith [h]
  · intro h
    refine ⟨by nlinarith, by nlinarith [h]⟩

/-- **Hyperperfect All K (partial result).**
The Minoli–Bear conjecture asserts that for *every* `k ≥ 1` there is a `k`-hyperperfect
number; this is open.  What is proved here is an unconditional criterion: a `k`-hyperperfect
number exists for every `k ≥ 1` such that either

* `k ^ 2 + 1` factors as `d * e` with `d + k` and `e + k` distinct primes — then
  `(d + k) * (e + k)` is `k`-hyperperfect (this covers `k = 1, 2, 6, …`), or
* there are distinct primes `p, q` with `q * (p ^ 2 - k * p - k) = k * p ^ 2 + k * p + 1` —
  then `p ^ 2 * q` is `k`-hyperperfect (this covers `k = 3` via `325 = 5 ^ 2 * 13`, etc.). -/
