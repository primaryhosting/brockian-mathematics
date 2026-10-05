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
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Finset

namespace Frontier

/-- The rank of a finite set `S` in a matroid `M`, as a natural number. -/

lemma matroidRank_boolMatroid (n : ℕ) (S : Finset (Fin n)) :
    matroidRank (boolMatroid n) S = S.card := by
  rw [matroidRank, Matroid.eRk_freeOn (Set.subset_univ _), Set.encard_coe_eq_coe_finsetCard]
  simp

/-- The characteristic polynomial of the Boolean matroid `U_{n,n}` is `(t - 1)^n`. -/
