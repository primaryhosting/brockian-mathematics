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

theorem indep_of_card_three (h4 : ∀ B : Finset (Fin 9), ¬ Gᶜ.IsNClique 4 B)
    (v : Fin 9) (T : Finset (Fin 9)) (hcard : T.card = 3) (hvT : v ∉ T)
    (hv : ∀ w ∈ T, ¬ G.Adj v w) (hTT : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ G.Adj x y) : False := by
  refine h4 (insert v T) ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
    rw [SimpleGraph.compl_adj]
    refine ⟨hxy, ?_⟩
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact hv _ hy
    · exact fun h => hv _ hx h.symm
    · exact hTT _ hx _ hy hxy
  · rw [Finset.card_insert_of_notMem hvT, hcard]

