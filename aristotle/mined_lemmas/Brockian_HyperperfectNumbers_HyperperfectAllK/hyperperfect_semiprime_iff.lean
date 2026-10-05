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

theorem hyperperfect_semiprime_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    IsHyperperfect k (p * q) ↔ p * q = k * (p + q) + 1 := by
  have h2p := hp.two_le
  have h2q := hq.two_le
  unfold IsHyperperfect
  rw [sum_divisors_mul_primes hp hq hpq]
  constructor
  · rintro ⟨-, h⟩
    nlinarith [h]
  · intro h
    refine ⟨?_, by nlinarith [h]⟩
    nlinarith

/-- **Main construction.** Every factorisation `d * e = k ^ 2 + 1` with `d + k` and `e + k`
distinct primes yields the `k`-hyperperfect number `(d + k) * (e + k)`. -/
