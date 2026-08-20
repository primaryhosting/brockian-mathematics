/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

/-- The *local constellation set* of a finite set `A ⊆ ℤ` with respect to a `k`-tuple of
displacements `d : Fin k → ℤ`: the set of base points `x ∈ A` such that the whole
constellation `x + d 0, …, x + d (k-1)` is contained in `A`. -/

noncomputable def constellationLocalCount (k : ℕ) (A : Finset ℤ) (d : Fin k → ℤ) : ℕ :=
  (constellationLocalSet k A d).card

/-- The *defect* of a single displacement `t`: the number of points of `A` that are not
translated back into `A` by `t`. -/
