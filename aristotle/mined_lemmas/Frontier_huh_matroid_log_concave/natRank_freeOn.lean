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

theorem natRank_freeOn {E S : Finset α} (h : S ⊆ E) :
    ((Matroid.freeOn (↑E : Set α)).eRk ↑S).toNat = S.card := by
  rw [Matroid.eRk_freeOn (by exact_mod_cast h), Set.encard_coe_eq_coe_finsetCard]
  simp

/-- The characteristic polynomial of the free (Boolean) matroid on an `n`-element set
is `(t - 1)^n`. -/
