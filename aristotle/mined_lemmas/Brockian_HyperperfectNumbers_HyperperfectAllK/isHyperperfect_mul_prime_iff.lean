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

theorem isHyperperfect_mul_prime_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    IsHyperperfect k (p * q) ↔ p * q = k * (p + q) + 1 := by
  constructor
  · rintro ⟨-, h⟩
    rw [show p * q = p ^ 1 * q by ring, sigma_primePow_mul_prime hp hq hpq] at h
    have h' : ((p ^ 1 * q + k * (p ^ 1 * q + 1) : ℕ) : ℤ)
        = ((k * ((∑ i ∈ Finset.range (1 + 1), (p : ℕ) ^ i) * (q + 1)) + 1 : ℕ) : ℤ) := by
      exact_mod_cast h
    simp [Finset.sum_range_succ] at h'
    have : (p : ℤ) * q = k * (p + q) + 1 := by linarith
    exact_mod_cast this
  · intro h
    have := isHyperperfect_primePow_mul_prime (k := k) (p := p) (q := q) (m := 1)
      hp hq hpq one_pos (by simpa [Finset.sum_range_succ, Nat.add_comm] using h)
    simpa using this

/-- **The classical hyperperfect family.** If `2 * p = 3 * k + 1` and `q = 3 * k + 4` with
`p` and `q` prime, then `p ^ 2 * q` is `k`-hyperperfect.  (This forces `k` to be odd.) -/
