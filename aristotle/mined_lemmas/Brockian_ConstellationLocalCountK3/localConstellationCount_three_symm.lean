/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The *local constellation count* of a set `S ⊆ ℕ` with respect to a pattern
`h : Fin k → ℕ` in the window `[0, N)`: the number of `n < N` such that the whole
translated constellation `n + h 0, …, n + h (k-1)` lies inside `S`. -/

theorem localConstellationCount_three_symm (S : Set ℕ) (a b c N : ℕ) :
    localConstellationCount S ![a, b, c] N = localConstellationCount S ![b, a, c] N ∧
    localConstellationCount S ![a, b, c] N = localConstellationCount S ![a, c, b] N := by
  classical
  rw [localConstellationCount_three, localConstellationCount_three,
    localConstellationCount_three]
  constructor
  · congr 1
    refine Finset.filter_congr ?_
    intro n _
    tauto
  · congr 1
    refine Finset.filter_congr ?_
    intro n _
    tauto

/--
**Constellation local count, `k = 3`.**

Extension of the local constellation count to `3`-tuples: for every set `S ⊆ ℕ`,
all shifts `a, b, c` and every window length `N`,

* the count is the number of `n < N` with `n + a, n + b, n + c ∈ S`;
* it is symmetric under permuting the three shifts;
* it is bounded above by the corresponding `2`-point count;
* it satisfies the union (Bonferroni) lower bound
  `N - (miss a + miss b + miss c) ≤ count`.
-/
