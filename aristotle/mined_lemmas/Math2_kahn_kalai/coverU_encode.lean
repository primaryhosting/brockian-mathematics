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

/-
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Basic definitions for the Kahn–Kalai theorem (Park–Pham proof):
the Bernoulli product measure on subsets of a finite ground set, covers,
`p`-smallness, up-sets, and the parameters `q(F)`, `p_c(F)`, `ℓ(F)`.
-/

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Bernoulli(`p`) product weight of a subset `A` inside the ground set `g`. -/

lemma coverU_encode {H : Finset (Finset α)} {k : ℕ} {W T : Finset α} (hk : ∀ S ∈ H, S.card ≤ k)
    (hT : T ∈ coverU H k W) :
    Disjoint T W ∧ T ⊆ shat H (W ∪ T) ∧ k < 2 * T.card ∧ T.card ≤ k := by
  simp only [coverU, Finset.mem_image, bigG, Finset.mem_filter] at hT
  obtain ⟨S, ⟨hSH, hSbig⟩, rfl⟩ := hT
  set T := frag H S W with hTdef
  have hdisj : Disjoint T W := frag_disjoint W hSH
  have hTS : T ⊆ S := frag_subset W hSH
  obtain ⟨S', hS'H, hS'sub, hS'eq⟩ := frag_spec W hSH
  have hS'Z : S' ⊆ W ∪ T := by
    intro x hx
    by_cases hxW : x ∈ W
    · exact Finset.mem_union_left _ hxW
    · refine Finset.mem_union_right _ ?_
      rw [hTdef, ← hS'eq]
      exact Finset.mem_sdiff.mpr ⟨hx, hxW⟩
  have hex : ∃ S₀ ∈ H, S₀ ⊆ W ∪ T := ⟨S', hS'H, hS'Z⟩
  have hShatH : shat H (W ∪ T) ∈ H := shat_mem hex
  have hShatZ : shat H (W ∪ T) ⊆ W ∪ T := shat_subset _ _
  have hcand : shat H (W ∪ T) \ W ∈ cands H S W := by
    refine mem_cands.mpr ⟨shat H (W ∪ T), hShatH, ?_, rfl⟩
    exact hShatZ.trans (Finset.union_subset_union_right hTS)
  have hcardle : T.card ≤ (shat H (W ∪ T) \ W).card := frag_min W hSH hcand
  have hsub : shat H (W ∪ T) \ W ⊆ T := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases Finset.mem_union.mp (hShatZ hx.1) with h | h
    · exact absurd h hx.2
    · exact h
  have heq : shat H (W ∪ T) \ W = T := Finset.eq_of_subset_of_card_le hsub hcardle
  refine ⟨hdisj, ?_, hSbig, le_trans (Finset.card_le_card hTS) (hk S hSH)⟩
  intro x hx
  have hx' : x ∈ shat H (W ∪ T) \ W := by rw [heq]; exact hx
  exact (Finset.mem_sdiff.mp hx').1

/-- Rewriting a sum over pairs `(W, T)` with `T ∈ coverU H k W` as an iterated sum. -/
