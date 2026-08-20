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

theorem isPrimeNat_iff_prime {p : ℕ} : IsPrimeNat p ↔ p.Prime := by
  constructor
  · rintro ⟨h2, hd⟩
    rw [Nat.prime_def]
    exact ⟨h2, fun d hd' => hd d hd'⟩
  · intro hp
    exact ⟨hp.two_le, fun d hd => (Nat.Prime.eq_one_or_self_of_dvd hp d hd)⟩

/-- **Erdős–Straus conjecture over `ℚ`, reduced to primes `p ≡ 1 (mod 4)`.**

If `4 / p = 1/x + 1/y + 1/z` is solvable in positive integers for every prime `p ≡ 1 (mod 4)`,
then it is solvable for every `n ≥ 2`. -/
