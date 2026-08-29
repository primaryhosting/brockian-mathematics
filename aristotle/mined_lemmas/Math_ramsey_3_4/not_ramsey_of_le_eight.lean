/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- `RamseyProp r s N` says: every simple graph on `N` vertices contains either a clique of
size `r` or an independent set of size `s` (i.e. an `s`-clique in the complement).
Equivalently: every 2-colouring of the edges of `K_N` has a red `K_r` or a blue `K_s`. -/

theorem not_ramsey_of_le_eight {N : ℕ} (hN : N ≤ 8) : ¬ RamseyProp 3 4 N := by
  intro h
  have hf : Function.Injective (Fin.castLE hN) := Fin.castLE_injective hN
  rcases h (W.comap (Fin.castLE hN)) with ⟨A, hA⟩ | ⟨B, hB⟩
  · exact W_no_tri _ (isNClique_image _ hf W A hA)
  · rw [comap_compl _ hf] at hB
    exact W_no_ind _ (isNClique_image _ hf Wᶜ B hB)

/-! ### The upper bound: every graph on 9 vertices has a triangle or an independent 4-set -/

section Upper

variable {G : SimpleGraph (Fin 9)}

