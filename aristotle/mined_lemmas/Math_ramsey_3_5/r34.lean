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

lemma r34 [DecidableRel G.Adj] {s : Finset V} (hs : 9 ≤ s.card) : Arrow G s 4 := by
  by_contra hcon
  rw [Arrow, not_or] at hcon
  obtain ⟨hno, hnoind⟩ := hcon
  obtain ⟨s', hs's, hs'card⟩ := Finset.exists_subset_card_eq hs
  have hno' : ¬ ∃ t ⊆ s', t.card = 3 ∧ IsCl G t := by
    rintro ⟨t, ht, h⟩
    exact hno ⟨t, ht.trans hs's, h⟩
  have hnoind' : ∀ t ⊆ s', t.card = 4 → ¬ IsInd G t := by
    intro t ht hc hi
    exact hnoind ⟨t, ht.trans hs's, hc, hi⟩
  have hdeg : ∀ v ∈ s', (Nb G s' v).card = 3 := by
    intro v hv
    have hsplit := card_Nb_add_card_Mb (G := G) hv
    have hle : (Nb G s' v).card ≤ 3 := by
      by_contra hgt
      push_neg at hgt
      obtain ⟨t, ht, htc, hti⟩ := indep_of_card_Nb hv (k := 4) (by omega) hno'
      exact hnoind' t ht htc hti
    have hge : 3 ≤ (Nb G s' v).card := by
      by_contra hlt
      push_neg at hlt
      have hM : 6 ≤ (Mb G s' v).card := by omega
      rcases r33 (G := G) hM with ⟨t, ht, htc, hti⟩ | ⟨t, ht, htc, hti⟩
      · exact hno' ⟨t, ht.trans Mb_subset, htc, hti⟩
      · obtain ⟨u, hu, huc, hui⟩ := indep_insert hv ht hti
        exact hnoind' u hu (by omega) hui
    omega
  have hsum : ∑ v ∈ s', (Nb G s' v).card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hs'card, smul_eq_mul]
  have hev := even_sum_deg G s'
  rw [hsum] at hev
  exact (by decide : ¬ Even 27) hev

/-- `R(3,5) ≤ 14`. -/
