/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-- The number of cells of `K` that contain the face `τ`. -/

theorem card_filter_powersetCard_pred (σ : Finset V) (P : Finset V → Prop) [DecidablePred P]
    (k : ℕ) (hcard : σ.card = k + 1) :
    ((Finset.powersetCard k σ).filter P).card = (σ.filter (fun x => P (σ.erase x))).card := by
  refine (Finset.card_bij (fun x _ => σ.erase x) ?_ ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hx ⊢
    refine ⟨⟨Finset.erase_subset _ _, ?_⟩, hx.2⟩
    rw [Finset.card_erase_of_mem hx.1, hcard]
    omega
  · intro x hx y hy hxy
    simp only [Finset.mem_filter] at hx hy
    dsimp only at hxy
    by_contra hne
    have hmem : x ∈ σ.erase y := Finset.mem_erase.2 ⟨hne, hx.1⟩
    rw [← hxy] at hmem
    exact (Finset.notMem_erase x σ) hmem
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hτ
    obtain ⟨⟨hsub, hc⟩, hP⟩ := hτ
    have h1 : (σ \ τ).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, hcard, hc]
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
    have hxmem : x ∈ σ \ τ := by rw [hx]; exact Finset.mem_singleton_self x
    have hxσ : x ∈ σ := (Finset.mem_sdiff.1 hxmem).1
    have hxτ : x ∉ τ := (Finset.mem_sdiff.1 hxmem).2
    have hτe : τ = σ.erase x := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        exact Finset.mem_erase.2 ⟨by rintro rfl; exact hxτ hy, hsub hy⟩
      · rw [Finset.card_erase_of_mem hxσ, hcard, hc]
        omega
    refine ⟨x, ?_, hτe.symm⟩
    simp only [Finset.mem_filter]
    exact ⟨hxσ, hτe ▸ hP⟩

/-- A rainbow cell has exactly one door. -/
