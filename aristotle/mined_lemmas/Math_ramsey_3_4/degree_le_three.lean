import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open SimpleGraph Finset

/-- `RamseyProp n k l` says that every simple graph on `n` vertices contains either a clique
of size `k` or an independent set (a clique of its complement) of size `l`. -/

theorem degree_le_three (h3 : G.CliqueFree 3) (h4 : Gᶜ.CliqueFree 4) (v : Fin 9) :
    (G.neighborFinset v).card ≤ 3 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨s, hs, hs4⟩ := Finset.exists_subset_card_eq (show 4 ≤ (G.neighborFinset v).card by omega)
  refine h4 s ⟨?_, hs4⟩
  intro a ha b hb hab
  have hva : G.Adj v a := by
    have := hs ha; rwa [SimpleGraph.mem_neighborFinset] at this
  have hvb : G.Adj v b := by
    have := hs hb; rwa [SimpleGraph.mem_neighborFinset] at this
  refine ⟨hab, fun hG => ?_⟩
  exact h3 {v, a, b} (SimpleGraph.is3Clique_triple_iff.2 ⟨hva, hvb, hG⟩)

/-- In a triangle-free graph on `9` vertices whose complement has no `4`-clique, every vertex
has degree at least `3`. -/
