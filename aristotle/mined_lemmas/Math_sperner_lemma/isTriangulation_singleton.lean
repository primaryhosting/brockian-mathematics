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

namespace Math

variable {V : Type*} [DecidableEq V]

/-- The `k`-dimensional faces (as `Finset`s of `k` vertices) occurring in the cells of `K`. -/

theorem isTriangulation_singleton :
    ∀ (n : ℕ) (A : Finset ℕ), A.card = n + 1 →
      IsTriangulation (V := ℕ) n A {A} (fun v => {v}) := by
  intro n
  induction n with
  | zero =>
    intro A hA
    refine ⟨hA, ⟨A, by simp⟩, by simp [hA], ?_, ?_⟩
    · intro s hs v hv
      rw [Finset.mem_singleton.mp hs] at hv
      simpa using hv
    · intro f hf
      simp only [facets, Finset.mem_biUnion, Finset.mem_singleton, Finset.mem_powersetCard] at hf
      obtain ⟨s, rfl, hfs, hfc⟩ := hf
      have hf0 : f = ∅ := Finset.card_eq_zero.mp hfc
      subst hf0
      rw [if_neg (by simp only [Finset.biUnion_empty]; intro h; rw [← h] at hA; simp at hA)]
      rw [Finset.filter_singleton, if_pos (Finset.empty_subset _)]
      simp
  | succ n ih =>
    intro A hA
    refine ⟨hA, ⟨A, by simp⟩, by simp [hA], ?_, ?_, ?_⟩
    · intro s hs v hv
      rw [Finset.mem_singleton.mp hs] at hv
      simpa using hv
    · intro f hf
      simp only [facets, Finset.mem_biUnion, Finset.mem_singleton, Finset.mem_powersetCard] at hf
      obtain ⟨s, rfl, hfs, hfc⟩ := hf
      have hne : f.biUnion (fun v => ({v} : Finset ℕ)) ≠ s := by
        rw [Finset.biUnion_singleton_eq_self]
        intro h; rw [h] at hfc; omega
      rw [if_neg hne, Finset.filter_singleton, if_pos hfs]
      simp
    · intro a ha
      have hcB : (A.erase a).card = n + 1 := by
        rw [Finset.card_erase_of_mem ha, hA]
        omega
      have hsub : subComplex (V := ℕ) {A} (fun v => {v}) (A.erase a) (n + 1) = {A.erase a} := by
        ext f
        simp only [subComplex, facets, Finset.mem_filter, Finset.mem_biUnion,
          Finset.mem_singleton, Finset.mem_powersetCard, Finset.biUnion_singleton_eq_self]
        constructor
        · rintro ⟨⟨s, rfl, hfs, hfc⟩, hsubB⟩
          exact Finset.eq_of_subset_of_card_le hsubB (by omega)
        · intro hfe
          subst hfe
          exact ⟨⟨A, rfl, Finset.erase_subset _ _, hcB⟩, Finset.Subset.refl _⟩
      rw [hsub]
      exact ih _ hcB

/-- The carrier function of a segment `[0,1]` subdivided at the midpoint: the vertex `0`
lies at the endpoint `0`, the vertex `2` at the endpoint `1`, and the vertex `1` in the
interior of the segment. -/
