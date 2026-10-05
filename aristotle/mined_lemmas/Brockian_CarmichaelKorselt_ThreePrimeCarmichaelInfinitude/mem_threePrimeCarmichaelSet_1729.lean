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

theorem mem_threePrimeCarmichaelSet_1729 : (1729 : ℕ) ∈ ThreePrimeCarmichaelSet := by
  have h : (1729 : ℕ) = (6 * 1 + 1) * (12 * 1 + 1) * (18 * 1 + 1) := by norm_num
  rw [h]
  exact chernick_mem_threePrimeCarmichaelSet Nat.one_pos (by norm_num) (by norm_num) (by norm_num)

/-- **Three Prime Carmichael Infinitude** (conditional on Chernick's hypothesis).

If there are infinitely many `k > 0` such that `6k+1`, `12k+1` and `18k+1` are all prime, then
there are infinitely many Carmichael numbers that are products of exactly three distinct primes.
The infinitude of three-factor Carmichael numbers is not known unconditionally; this is a
Lean-checked reduction of it to a prime-tuple hypothesis. -/
