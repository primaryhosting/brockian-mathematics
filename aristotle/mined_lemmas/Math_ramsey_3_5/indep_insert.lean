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

lemma indep_insert {s : Finset V} {v : V} (hv : v ∈ s) {T : Finset V}
    (hT : T ⊆ Mb G s v) (hTind : IsInd G T) :
    ∃ t ⊆ s, t.card = T.card + 1 ∧ IsInd G t := by
  have hvT : v ∉ T := by
    intro h
    have := hT h
    simp [Mb, Finset.mem_filter, Finset.mem_erase] at this
  refine ⟨insert v T, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv
    · exact Mb_subset (hT hx)
  · rw [Finset.card_insert_of_notMem hvT]
  · intro a ha b hb hab
    have key : ∀ c ∈ T, ¬ G.Adj v c := by
      intro c hc
      have := hT hc
      simp only [Mb, Finset.mem_filter, Finset.mem_erase] at this
      exact this.2
    rw [Finset.mem_insert] at ha hb
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · subst ha; exact key b hb
    · rcases hb with hb | hb
      · subst hb; exact fun h => key a ha h.symm
      · exact hTind a ha b hb hab

/-! ## The handshake parity lemma -/

