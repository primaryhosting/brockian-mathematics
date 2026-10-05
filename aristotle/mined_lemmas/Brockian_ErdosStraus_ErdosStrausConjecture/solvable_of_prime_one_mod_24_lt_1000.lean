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

theorem solvable_of_prime_one_mod_24_lt_1000 {p : ℕ} (hp : p.Prime) (h1 : p % 24 = 1)
    (h2 : p < 1000) : Solvable p := by
  obtain ⟨j, rfl⟩ : ∃ j, p = 24 * j + 1 := ⟨p / 24, by omega⟩
  have hj : j < 42 := by omega
  interval_cases j <;>
    first
      | (exfalso; revert hp; norm_num; done)
      | exact solvable_73
      | exact solvable_97
      | exact solvable_193
      | exact solvable_241
      | exact solvable_313
      | exact solvable_337
      | exact solvable_409
      | exact solvable_433
      | exact solvable_457
      | exact solvable_577
      | exact solvable_601
      | exact solvable_673
      | exact solvable_769
      | exact solvable_937

/-- **Unconditional partial result.** The Erdős–Straus conjecture holds for all
`2 ≤ n < 1000`. -/
