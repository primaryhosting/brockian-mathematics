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

theorem ConstellationLocalCountK3 (A : Finset G) :
    constellationLocalCount A 3 =
      ∑ d : G, (A.filter (fun x => x + d ∈ A ∧ x + (2 : ℕ) • d ∈ A)).card := by
  rw [constellationLocalCount_three_eq_filter]
  rw [Finset.card_filter]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.card_filter, ← Finset.sum_subset (Finset.subset_univ A) (by intro x _ hx; simp [hx])]
  exact Finset.sum_congr rfl fun x hx => by simp [hx]

/-- The local constellation count is antitone in `k`: longer progressions are rarer.
In particular the `k = 3` count is at most the `k = 2` count. -/
