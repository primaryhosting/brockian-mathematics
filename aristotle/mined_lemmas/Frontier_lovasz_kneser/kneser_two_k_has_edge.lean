import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
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

set_option grind.warning false

namespace Frontier

/-- Vertices of the Kneser graph `KG_{n,k}`: the `k`-element subsets of an `n`-element set. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-subsets of `Fin n`, and two
distinct vertices are adjacent when the corresponding sets are disjoint. -/

lemma kneser_two_k_has_edge (k : ℕ) (hk : 1 ≤ k) :
    ∃ s t : KneserVertex (2 * k) k, (kneserGraph (2 * k) k).Adj s t := by
  have h1 : ∀ m ∈ Finset.range k, m < 2 * k := by
    intro m hm
    simp only [Finset.mem_range] at hm
    omega
  have h2 : ∀ m ∈ Finset.Ico k (2 * k), m < 2 * k := by
    intro m hm
    simp only [Finset.mem_Ico] at hm
    omega
  refine ⟨⟨(Finset.range k).attachFin h1, by rw [Finset.card_attachFin, Finset.card_range]⟩,
    ⟨(Finset.Ico k (2 * k)).attachFin h2, by
      rw [Finset.card_attachFin, Nat.card_Ico]; omega⟩, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_attachFin, Finset.mem_range] at ha
    rw [Finset.mem_attachFin, Finset.mem_Ico] at hb
    omega
  · intro h
    have hv := congrArg Subtype.val h
    simp only at hv
    have h0 : (⟨0, by omega⟩ : Fin (2 * k)) ∈ (Finset.range k).attachFin h1 := by
      rw [Finset.mem_attachFin, Finset.mem_range]
      exact hk
    rw [hv, Finset.mem_attachFin, Finset.mem_Ico] at h0
    have h0' : k ≤ 0 := h0.1
    omega

