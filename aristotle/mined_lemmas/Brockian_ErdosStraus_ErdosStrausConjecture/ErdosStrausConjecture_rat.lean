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

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `IsErdosStrausRepresentable n` says that `4 / n` is a sum of three positive unit fractions,
`4 / n = 1 / x + 1 / y + 1 / z`, written here in the equivalent denominator-cleared form
`4 * (x * y * z) = n * (y * z + x * z + x * y)` with `x, y, z > 0`.
(The three denominators are not required to be distinct.) -/

theorem ErdosStrausConjecture_rat
    (hprime : ∀ p : ℕ, p.Prime → p % 4 = 1 → IsErdosStrausRepresentableRat p)
    (n : ℕ) (hn : 2 ≤ n) : IsErdosStrausRepresentableRat n := by
  rw [← isErdosStrausRepresentable_iff_rat (by omega)]
  refine ErdosStrausConjecture (fun p hp h1 => ?_) n hn
  have hp' : p.Prime := isPrimeNat_iff_prime.mp hp
  exact (isErdosStrausRepresentable_iff_rat hp'.pos).mpr (hprime p hp' h1)

/-- Unconditional partial result over `ℚ`: `4/n` is a sum of three unit fractions whenever
`n ≥ 2` and `n % 4 ≠ 1`. -/
