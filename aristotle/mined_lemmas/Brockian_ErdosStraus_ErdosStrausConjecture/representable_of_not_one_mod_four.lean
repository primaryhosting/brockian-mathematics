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

theorem representable_of_not_one_mod_four {n : Nat} (hn : 2 ≤ n) (h : n % 4 ≠ 1) :
    IsErdosStrausRepresentable n := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · exact representable_of_even (by omega) ⟨n / 2, by omega⟩
  · exact representable_of_three_mod_four (by omega)

/-- **Erdős–Straus conjecture, reduced to primes `p ≡ 1 (mod 4)`.**

For every `n ≥ 2` the fraction `4 / n` is a sum of three positive unit fractions, provided this
is known for every prime `p ≡ 1 (mod 4)`. All the remaining cases (`p = 2` and `p ≡ 3 mod 4`)
are settled unconditionally here, so this is a complete Lean-checked reduction of the
Erdős–Straus conjecture to the case of primes congruent to `1` modulo `4`. -/
