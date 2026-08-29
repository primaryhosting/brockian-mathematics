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

lemma solvable_of_three_mod_four {n : ℕ} (hn : n % 4 = 3) : Solvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  refine solvable_of_pair (by omega : 0 < k + 1)
    (by positivity : 0 < (k + 1) * (4 * k + 3)) ?_
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hn' : (4 * (k : ℚ) + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Case `n ≡ 2 [MOD 3]`: with `n = 3k+2`, `4/n = 1/(k+1) + 1/n + 1/(n(k+1))`. -/
