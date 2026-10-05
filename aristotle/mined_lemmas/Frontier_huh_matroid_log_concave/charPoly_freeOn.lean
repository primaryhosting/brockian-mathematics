/-
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
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

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The characteristic polynomial of a matroid `M` with finite ground set `E`, in its
Whitney rank-generating form
`χ_M(t) = ∑_{S ⊆ E} (-1)^{|S|} t^{r(E) - r(S)}`. -/

theorem charPoly_freeOn (E : Finset α) :
    charPoly (Matroid.freeOn (↑E : Set α)) E = (X - 1) ^ E.card := by
  classical
  have hE : (X - 1 : Polynomial ℤ) ^ E.card = ∏ _i ∈ E, ((-1 : Polynomial ℤ) + X) := by
    rw [Finset.prod_const]
    ring
  rw [charPoly, hE, Finset.prod_add]
  refine Finset.sum_congr rfl ?_
  intro t ht
  have hsub : t ⊆ E := Finset.mem_powerset.mp ht
  rw [Finset.prod_const, Finset.prod_const, Finset.card_sdiff_of_subset hsub,
    natRank_freeOn (Finset.Subset.refl E), natRank_freeOn hsub]

/-- The Whitney numbers of the free matroid on `E` are the binomial coefficients. -/
