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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `Solvable n` means that `4 / n` can be written as a sum of three unit fractions
with positive (natural) denominators. -/

lemma solvable_of_two_mod_three {n : ℕ} (hn : n % 3 = 2) : Solvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  refine ⟨k + 1, 3 * k + 2, (3 * k + 2) * (k + 1), by omega, by omega, by positivity, ?_⟩
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hn' : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Case `n ≡ 13 [MOD 24]`: with `n = 24t+13`,
`4/n = 1/(6t+4) + 1/(48t²+58t+18) + 1/(2(24t+13)(3t+2)(24t²+29t+9))`.

(This comes from `4/n = 1/x + 3/(nx)` with `x = (n+3)/4`, followed by
`3/m = 1/((m+2)/3) + 1/(m(m+2)/6)`, which is legitimate exactly when `m = nx`
is even and `m ≡ 1 [MOD 3]`.) -/
