/-
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
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

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The information cell of an agent at state `ω`: the set of states the agent, whose
information is described by the signal map `I`, cannot distinguish from `ω`. -/

theorem mass_inter_eq_of_cells {κ : Type*} [DecidableEq κ]
    (w : Ω → ℝ) (E : Finset Ω) (I : Ω → κ) (q : ℝ) :
    ∀ C : Finset Ω, (∀ ω ∈ C, cell I ω ⊆ C) →
      (∀ ω ∈ C, ∑ x ∈ cell I ω ∩ E, w x = q * ∑ x ∈ cell I ω, w x) →
      ∑ x ∈ C ∩ E, w x = q * ∑ x ∈ C, w x := by
  intro C
  induction C using Finset.strongInduction with
  | _ C ih =>
    intro hC h
    rcases C.eq_empty_or_nonempty with rfl | ⟨ω, hω⟩
    · simp
    · set K : Finset Ω := cell I ω with hKdef
      have hKC : K ⊆ C := hC ω hω
      have hωK : ω ∈ K := self_mem_cell I ω
      have hDsub : C \ K ⊂ C := by
        refine Finset.ssubset_iff_of_subset (Finset.sdiff_subset) |>.2 ⟨ω, hω, ?_⟩
        simp [hωK]
      -- the complement of the cell inside `C` is again a union of cells
      have hD : ∀ ω' ∈ C \ K, cell I ω' ⊆ C \ K := by
        intro ω' hω' x hx
        rw [Finset.mem_sdiff] at hω'
        obtain ⟨hω'C, hω'K⟩ := hω'
        rw [Finset.mem_sdiff]
        refine ⟨hC ω' hω'C hx, ?_⟩
        intro hxK
        apply hω'K
        simp only [hKdef, mem_cell] at hxK ⊢
        simp only [mem_cell] at hx
        rw [← hx, hxK]
      have hDh : ∀ ω' ∈ C \ K, ∑ x ∈ cell I ω' ∩ E, w x = q * ∑ x ∈ cell I ω', w x := by
        intro ω' hω'
        exact h ω' (Finset.mem_sdiff.1 hω').1
      have hrec : ∑ x ∈ (C \ K) ∩ E, w x = q * ∑ x ∈ C \ K, w x := ih (C \ K) hDsub hD hDh
      have hsplit : ∑ x ∈ C \ K, w x + ∑ x ∈ K, w x = ∑ x ∈ C, w x :=
        Finset.sum_sdiff hKC
      have hKE : K ∩ E ⊆ C ∩ E := Finset.inter_subset_inter_right hKC
      have hset : (C ∩ E) \ (K ∩ E) = (C \ K) ∩ E := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      have hsplitE : ∑ x ∈ (C \ K) ∩ E, w x + ∑ x ∈ K ∩ E, w x = ∑ x ∈ C ∩ E, w x := by
        rw [← hset]
        exact Finset.sum_sdiff hKE
      have hK : ∑ x ∈ K ∩ E, w x = q * ∑ x ∈ K, w x := h ω hω
      rw [← hsplitE, hrec, hK, ← hsplit]
      ring

/-- **Aumann's agreement theorem** (finite state space, common prior).

`w` is a common prior on the finite state space `Ω`, assigning positive weight to every state
of the event `C`.  The two agents' information partitions are described by the signal maps
`I₁` and `I₂`, so that agent `i` cannot distinguish the states inside `cell Iᵢ ω`.

`C` is a *common knowledge* event: it is a union of cells of each agent (`hC₁`, `hC₂`); this is
exactly the condition that, at any state of `C`, it is common knowledge that the true state lies
in `C`.  Throughout `C`, agent `1`'s posterior probability of the event `E` equals `q₁` and
agent `2`'s equals `q₂`, i.e. the posteriors are common knowledge.

Conclusion: the posteriors agree, `q₁ = q₂`.  The agents cannot agree to disagree.

(The prior is not required to be normalized: the statement is invariant under rescaling `w`,
so it covers in particular the case `∑ x, w x = 1`.) -/
