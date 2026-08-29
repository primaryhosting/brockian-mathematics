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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Brockian.CarmichaelKorselt

/-- A Carmichael number: a composite `n > 1` which is a Fermat pseudoprime to every base
coprime to it. -/

theorem mem_threePrimeCarmichaelSet_561 : (561 : ℕ) ∈ ThreePrimeCarmichaelSet := by
  have h : (561 : ℕ) = 3 * 11 * 17 := by norm_num
  rw [h]
  exact ⟨isCarmichael_of_three_primes (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    3, 11, 17, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩

/-- The hypothesis is satisfiable: `k = 1` gives the Carmichael number `1729 = 7 * 13 * 19`. -/
