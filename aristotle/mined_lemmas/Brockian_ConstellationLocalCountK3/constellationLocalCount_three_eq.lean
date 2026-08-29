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

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The set of base points `x` of a translate of the shift `d` landing inside `S`,
i.e. `{x | x + d ∈ S}`. -/

theorem constellationLocalCount_three_eq (S : Finset G) (d : Fin 3 → G) :
    constellationLocalCount S d =
      (shiftPreimage S (d 0) ∩ shiftPreimage S (d 1) ∩ shiftPreimage S (d 2)).card := by
  unfold constellationLocalCount
  congr 1
  ext x
  simp [shiftPreimage, Fin.forall_fin_succ]

/-- **Constellation local count, `k = 3`.**

In a finite abelian group `G`, for any finite set `S` and any triple of shifts
`d : Fin 3 → G`, the number of base points `x` with `x + d 0, x + d 1, x + d 2` all in `S`
satisfies the Bonferroni-type lower bound
`3 * |S| ≤ count + 2 * |G|`.

This extends the (trivial) `k = 1` count `|S|` and the `k = 2` count
`|S| + |S| ≤ count + |G|` to triples. -/
