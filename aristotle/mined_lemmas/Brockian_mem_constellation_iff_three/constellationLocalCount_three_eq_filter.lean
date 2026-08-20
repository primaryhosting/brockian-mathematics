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

lemma constellationLocalCount_three_eq_filter (A : Finset G) :
    constellationLocalCount A 3 =
      (Finset.univ.filter
        (fun p : G × G => p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + (2 : ℕ) • p.2 ∈ A)).card := by
  unfold constellationLocalCount
  congr 1
  apply Finset.filter_congr
  intro p _
  simpa using mem_constellation_iff_three A p.1 p.2

/-- **Constellation local count, `k = 3`.** The number of `3`-term progressions
`(x, x + d, x + 2d)` contained in a finite set `A` of an abelian group is obtained by
summing, over all common differences `d`, the number of `x ∈ A` with `x + d ∈ A` and
`x + 2d ∈ A`.

The proof reduces the cardinality to a double sum of indicators
(`Finset.card_filter`, `Fintype.sum_prod_type`) and exchanges the order of summation
(`Finset.sum_comm`). -/
