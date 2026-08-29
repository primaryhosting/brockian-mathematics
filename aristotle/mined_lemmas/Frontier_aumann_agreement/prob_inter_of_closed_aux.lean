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

variable {Ω : Type*} [DecidableEq Ω]

/-- The probability of the (finite) event `S` under the weight function `p`. -/

private lemma prob_inter_of_closed_aux (hI : IsPartition I) :
    ∀ (n : ℕ) (M : Finset Ω), M.card ≤ n → (∀ ω ∈ M, I ω ⊆ M) →
      (∀ ω ∈ M, prob p (E ∩ I ω) = q * prob p (I ω)) →
      prob p (E ∩ M) = q * prob p M := by
  intro n
  induction n with
  | zero =>
      intro M hcard _ _
      have : M = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst this
      simp
  | succ n ih =>
      intro M hcard hclosed hq
      rcases M.eq_empty_or_nonempty with rfl | ⟨ω, hω⟩
      · simp
      · set C : Finset Ω := I ω with hCdef
        have hCM : C ⊆ M := hclosed ω hω
        have hωC : ω ∈ C := hI.mem_self ω
        set M' : Finset Ω := M \ C with hM'def
        -- the complement `M'` is still a union of cells
        have hclosed' : ∀ ω' ∈ M', I ω' ⊆ M' := by
          intro ω' hω' x hx
          have hω'M : ω' ∈ M := (Finset.mem_sdiff.mp hω').1
          have hω'C : ω' ∉ C := (Finset.mem_sdiff.mp hω').2
          refine Finset.mem_sdiff.mpr ⟨hclosed ω' hω'M hx, ?_⟩
          intro hxC
          have h1 : I x = I ω' := hI.eq_of_mem ω' x hx
          have h2 : I x = C := hI.eq_of_mem ω x hxC
          have h3 : I ω' = C := by rw [← h1, h2]
          exact hω'C (h3 ▸ hI.mem_self ω')
        have hcard' : M'.card ≤ n := by
          have hlt : M'.card < M.card := by
            refine Finset.card_lt_card ?_
            refine ⟨Finset.sdiff_subset, ?_⟩
            intro hsub
            exact (Finset.mem_sdiff.mp (hsub (hCM hωC))).2 hωC
          omega
        have hq' : ∀ ω' ∈ M', prob p (E ∩ I ω') = q * prob p (I ω') := by
          intro ω' hω'
          exact hq ω' (Finset.mem_sdiff.mp hω').1
        have hrec : prob p (E ∩ M') = q * prob p M' := ih M' hcard' hclosed' hq'
        -- split the probabilities along `M = C ⊔ M'`
        have hsplit : prob p M' + prob p C = prob p M := Finset.sum_sdiff hCM
        have hEsplit : prob p (E ∩ M') + prob p (E ∩ C) = prob p (E ∩ M) := by
          have hsub : E ∩ C ⊆ E ∩ M := Finset.inter_subset_inter_left hCM
          have hset : (E ∩ M) \ (E ∩ C) = E ∩ M' := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_inter, hM'def]
            tauto
          have := Finset.sum_sdiff (f := p) hsub
          rw [hset] at this
          exact this
        have hqC : prob p (E ∩ C) = q * prob p C := hq ω hω
        calc prob p (E ∩ M) = prob p (E ∩ M') + prob p (E ∩ C) := hEsplit.symm
          _ = q * prob p M' + q * prob p C := by rw [hrec, hqC]
          _ = q * (prob p M' + prob p C) := by ring
          _ = q * prob p M := by rw [hsplit]

