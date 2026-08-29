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

lemma r32 [DecidableRel G.Adj] {s : Finset V} (hs : 3 ≤ s.card) : Arrow G s 2 := by
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hs
  by_cases h : IsCl G t
  · exact Or.inl ⟨t, hts, htc, h⟩
  · unfold IsCl at h
    push_neg at h
    obtain ⟨a, ha, b, hb, hab, hadj⟩ := h
    refine Or.inr ⟨{a, b}, ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hts ha
      · exact hts hb
    · rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    · intro x hx y hy hxy
      rw [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hadj
      · exact fun h => hadj h.symm
      · exact absurd rfl hxy

/-- `R(3,3) ≤ 6`. -/
