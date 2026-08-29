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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Math

/-! ## Basic notions: cliques and independent sets relative to a finite vertex set -/

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- `IsCl G t` says that the finite set `t` is a clique of `G`. -/

lemma r35 [DecidableRel G.Adj] {s : Finset V} (hs : 14 ≤ s.card) : Arrow G s 5 := by
  by_cases hno : ∃ t ⊆ s, t.card = 3 ∧ IsCl G t
  · exact Or.inl hno
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hN : 5 ≤ (Nb G s v).card
  · exact Or.inr (indep_of_card_Nb hv hN hno)
  push_neg at hN
  have hsplit := card_Nb_add_card_Mb (G := G) hv
  have hM : 9 ≤ (Mb G s v).card := by omega
  rcases r34 (G := G) hM with ⟨t, ht, htc, hti⟩ | ⟨t, ht, htc, hti⟩
  · exact absurd ⟨t, ht.trans Mb_subset, htc, hti⟩ hno
  · obtain ⟨u, hu, huc, hui⟩ := indep_insert hv ht hti
    exact Or.inr ⟨u, hu, by omega, hui⟩

/-! ## The lower bound: an explicit graph on 13 vertices -/

/-- Adjacency of the circulant graph `C₁₃(1,5)`. -/
