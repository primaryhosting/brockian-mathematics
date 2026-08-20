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
/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists

(The header block above is repeated here as a module docstring: Lean requires `import`
commands to precede any doc comment, so the file-opening header is an ordinary comment.)

Unitary divisors, the unitary divisor sum `σ*`, unitary perfect numbers, verification of the
five known unitary perfect numbers, the fact that no odd number `> 1` is unitary perfect, and
a reduction of the open "sixth unitary perfect number" problem.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d ∣ n` with `gcd (d, n / d) = 1`. -/

theorem unitaryPerfect_two_pow_mul_iff {a m : ℕ} (ha : 1 ≤ a) (hm : Odd m) (hm0 : 0 < m) :
    IsUnitaryPerfect (2 ^ a * m) ↔ (2 ^ a + 1) * sigmaStar m = 2 ^ (a + 1) * m := by
  have hcop : Nat.Coprime (2 ^ a) m := (Nat.coprime_two_left.mpr hm).pow_left _
  have hs : sigmaStar (2 ^ a * m) = (2 ^ a + 1) * sigmaStar m :=
    sigmaStar_prime_pow_mul Nat.prime_two (by omega) hm0 hcop
  constructor
  · rintro ⟨-, hperf⟩
    rw [hs] at hperf
    rw [hperf, pow_succ]
    ring
  · intro hrel
    refine ⟨by positivity, ?_⟩
    rw [hs, hrel, pow_succ]
    ring

/-- If `2 ^ a * p ^ k` (with `a, k ≥ 1`, `p` an odd prime) is unitary perfect, then it is `6`. -/
