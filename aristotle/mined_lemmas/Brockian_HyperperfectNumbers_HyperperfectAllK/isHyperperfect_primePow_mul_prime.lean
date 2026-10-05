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

import Mathlib

/-!
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-! ## The notion of a `k`-hyperperfect number -/

/-- `IsHyperperfect k n` says that `n` is a `k`-hyperperfect number, i.e. `n > 1` and
`n = 1 + k * (σ n - n - 1)`, where `σ n` is the sum of the divisors of `n`.

The equation is written in the subtraction-free form `n + k * (n + 1) = k * σ n + 1`,
which is equivalent over `ℤ` to `n = 1 + k * (σ n - n - 1)`; this avoids the pitfalls of
truncated natural subtraction (which would make `n = 1` a spurious solution). -/

theorem isHyperperfect_primePow_mul_prime {k p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hm : 0 < m)
    (hcert : p ^ m * q = k * (∑ i ∈ Finset.range m, p ^ i) * (q + p) + 1) :
    IsHyperperfect k (p ^ m * q) := by
  set S : ℕ := ∑ i ∈ Finset.range m, p ^ i with hS
  refine ⟨?_, ?_⟩
  · -- `p ^ m * q > 1`
    have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.one_lt
    have h2 : 1 ≤ q := hq.one_lt.le.trans' (by norm_num)
    calc 1 < p ^ m := h1
      _ = p ^ m * 1 := by ring
      _ ≤ p ^ m * q := Nat.mul_le_mul_left _ h2
  · -- the defining equation
    rw [sigma_primePow_mul_prime hp hq hpq, Finset.sum_range_succ, ← hS]
    have hgeom : p * S + 1 = S + p ^ m := geom_sum_step p m
    have hcert' : ((p : ℤ)) ^ m * q = k * S * (q + p) + 1 := by exact_mod_cast hcert
    have hgeom' : (p : ℤ) * S + 1 = (S : ℤ) + (p : ℤ) ^ m := by exact_mod_cast hgeom
    have key : ((p ^ m * q + k * (p ^ m * q + 1) : ℕ) : ℤ)
        = ((k * ((S + p ^ m) * (q + 1)) + 1 : ℕ) : ℤ) := by
      push_cast
      linear_combination hcert' + (k : ℤ) * hgeom'
    exact_mod_cast key

/-- **Semiprime criterion.** For distinct primes `p ≠ q`, the number `p * q` is
`k`-hyperperfect if and only if `p * q = k * (p + q) + 1`. -/
