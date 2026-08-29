import Mathlib
import RequestProject.KahnKalai.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Expectation and threshold are within a log factor: a formalisation of the Park–Pham proof
of the Kahn–Kalai conjecture.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased measure of a family of subsets. -/

lemma frag_subset_edgeIn {W S : Finset α} (hS : S ∈ H) :
    frag H W S ⊆ edgeIn H (W ∪ frag H W S) := by
  have hex : ∃ R ∈ H, R ⊆ W ∪ frag H W S := frag_exists_edge hS
  set T := frag H W S with hTdef
  have hmem := edgeIn_mem H hex
  have hsub := edgeIn_subset H hex
  set Sh := edgeIn H (W ∪ T) with hSh
  have hTW : Disjoint T W := frag_disjoint H hS
  -- `Sh \ W ⊆ T`
  have h1 : Sh \ W ⊆ T := by
    intro y hy
    simp only [Finset.mem_sdiff] at hy
    rcases Finset.mem_union.1 (hsub hy.1) with h | h
    · exact absurd h hy.2
    · exact h
  -- `Sh \ W` is a candidate fragment, so `|T| ≤ |Sh \ W|`
  have h2 : Sh \ W ∈ cand H W S := by
    simp only [cand, Finset.mem_image, Finset.mem_filter]
    refine ⟨Sh, ⟨hmem, ?_⟩, rfl⟩
    intro y hy
    rcases Finset.mem_union.1 (hsub hy) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (frag_subset H hS h)
  have h3 : T.card ≤ (Sh \ W).card := frag_min H hS _ h2
  have h4 : Sh \ W = T := Finset.eq_of_subset_of_card_le h1 h3
  intro y hy
  have : y ∈ Sh \ W := by rw [h4]; exact hy
  exact (Finset.mem_sdiff.1 this).1

