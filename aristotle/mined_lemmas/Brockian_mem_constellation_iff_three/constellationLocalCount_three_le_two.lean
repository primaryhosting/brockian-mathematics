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

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The local constellation count of order `k` of a finite set `A` in an abelian group:
the number of pairs `(x, d)` such that the `k`-term arithmetic progression
`x, x + d, …, x + (k-1) • d` lies entirely in `A`. -/

theorem constellationLocalCount_three_le_two (A : Finset G) :
    constellationLocalCount A 3 ≤ constellationLocalCount A 2 := by
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact fun i hi => hp i (by omega)

/-- Trivial (`d = 0`) constellations give the lower bound `|A| ≤` the `k = 3` count. -/
