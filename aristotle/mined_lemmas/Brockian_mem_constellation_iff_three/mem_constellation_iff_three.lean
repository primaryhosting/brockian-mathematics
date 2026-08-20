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

lemma mem_constellation_iff_three (A : Finset G) (x d : G) :
    (∀ i < 3, x + i • d ∈ A) ↔ x ∈ A ∧ x + d ∈ A ∧ x + (2 : ℕ) • d ∈ A := by
  constructor
  · intro h
    refine ⟨?_, ?_, h 2 (by norm_num)⟩
    · simpa using h 0 (by norm_num)
    · simpa using h 1 (by norm_num)
  · rintro ⟨h0, h1, h2⟩ i hi
    interval_cases i
    · simpa using h0
    · simpa using h1
    · exact h2

/-- The `k = 3` local constellation count as a count over pairs, with the progression
condition written out explicitly. -/
