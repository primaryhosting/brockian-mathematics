import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The *local constellation count* of the shift pattern (constellation) `h : Fin k → ℤ`
relative to a set `S` of integers, counted over the window `I`:
the number of `x ∈ I` such that all the shifted points `x + h i` lie in `S`. -/

theorem ConstellationLocalCountK3 (S I : Finset ℤ) (h0 h1 h2 : ℤ) :
    constLocalCount S I ![h0, h1, h2] =
        (I.filter (fun x => x + h0 ∈ S ∧ x + h1 ∈ S ∧ x + h2 ∈ S)).card ∧
      constLocalCount S I ![h0, h1, h2] ≤ constLocalCount S I ![h0, h1] ∧
      constLocalCount S I ![h0, h1] ≤ constLocalCount S I ![h0] ∧
      (I.filter (fun x => x + h0 ∈ S)).card + (I.filter (fun x => x + h1 ∈ S)).card
          + (I.filter (fun x => x + h2 ∈ S)).card
        ≤ constLocalCount S I ![h0, h1, h2] + 2 * I.card := by
  classical
  refine ⟨constLocalCount_three S I h0 h1 h2, constLocalCount_three_le_two S I h0 h1 h2, ?_, ?_⟩
  · rw [constLocalCount_two, constLocalCount_one]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.1⟩
  · have h12 := card_filter_and_ge I (fun x => x + h0 ∈ S) (fun x => x + h1 ∈ S)
    have h123 := card_filter_and_ge I (fun x => x + h0 ∈ S ∧ x + h1 ∈ S)
      (fun x => x + h2 ∈ S)
    rw [constLocalCount_three]
    have hrw : (I.filter (fun x => (x + h0 ∈ S ∧ x + h1 ∈ S) ∧ x + h2 ∈ S)).card
        = (I.filter (fun x => x + h0 ∈ S ∧ x + h1 ∈ S ∧ x + h2 ∈ S)).card := by
      congr 1
      apply Finset.filter_congr
      intro x _
      simp [and_assoc]
    rw [hrw] at h123
    omega

end Brockian

