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

theorem three_le_degree (h3 : G.CliqueFree 3) (h4 : Gᶜ.CliqueFree 4) (v : Fin 9) :
    3 ≤ (G.neighborFinset v).card := by
  by_contra hcon
  push_neg at hcon
  set T : Finset (Fin 9) := (Finset.univ : Finset (Fin 9)) \ insert v (G.neighborFinset v) with hT
  have hvnb : v ∉ G.neighborFinset v := by simp
  have hcardins : (insert v (G.neighborFinset v)).card = (G.neighborFinset v).card + 1 := by
    rw [Finset.card_insert_of_notMem hvnb]
  have hcardT : 6 ≤ T.card := by
    have h1 : T.card = 9 - (insert v (G.neighborFinset v)).card := by
      rw [hT, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp
    omega
  obtain ⟨s, hsT, hs⟩ := exists_indep_three_of_six h3 T hcardT
  have hvs : ∀ b ∈ s, Gᶜ.Adj v b := by
    intro b hb
    have hbT := hsT hb
    rw [hT, Finset.mem_sdiff] at hbT
    have hb' : b ∉ insert v (G.neighborFinset v) := hbT.2
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hb'
    exact ⟨fun h => hb'.1 h.symm, hb'.2⟩
  exact h4 (insert v s) (hs.insert hvs)

/-- The upper bound `R(3,4) ≤ 9`. -/
