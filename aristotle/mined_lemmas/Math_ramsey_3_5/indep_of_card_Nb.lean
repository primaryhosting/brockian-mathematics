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

lemma indep_of_card_Nb {s : Finset V} {v : V} (hv : v ∈ s) {k : ℕ}
    (hk : k ≤ (Nb G s v).card)
    (hno : ¬ ∃ t ⊆ s, t.card = 3 ∧ IsCl G t) :
    ∃ t ⊆ s, t.card = k ∧ IsInd G t := by
  have hNind : IsInd G (Nb G s v) := by
    intro a ha b hb hab hadj
    simp only [Nb, Finset.mem_filter] at ha hb
    refine hno ⟨{v, a, b}, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv
      · exact ha.1
      · exact hb.1
    · have hva : v ≠ a := fun h => G.irrefl (h ▸ ha.2)
      have hvb : v ≠ b := fun h => G.irrefl (h ▸ hb.2)
      rw [Finset.card_insert_of_notMem (by simp [hva, hvb]),
        Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    · intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxy
          | exact ha.2
          | exact hb.2
          | exact ha.2.symm
          | exact hb.2.symm
          | exact hadj
          | exact hadj.symm
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hk
  exact ⟨t, hts.trans Nb_subset, htc, hNind.subset hts⟩

/-- Adding `v` to an independent set of non-neighbours of `v` keeps it independent. -/
