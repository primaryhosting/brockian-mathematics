import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Ramsey

/-- A `b`-monochromatic set of vertices for the edge colouring `c`. -/

lemma arrow_two_right {c : ℕ → ℕ → Bool} (hsym : ∀ x y, c x y = c y x) {s : Finset ℕ} {p : ℕ}
    (hp : p ≤ s.card) : Arrows c s p 2 := by
  by_cases h : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ c x y = false
  · obtain ⟨x, hx, y, hy, hxy, hc⟩ := h
    refine Or.inr ⟨{x, y}, ?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · rw [Finset.mem_singleton] at hz; exact hz ▸ hy
    · rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hc
      · rw [hsym]; exact hc
      · exact absurd rfl hab
  · push_neg at h
    obtain ⟨t, hts, hcard⟩ := Finset.exists_subset_card_eq hp
    refine Or.inl ⟨t, hts, hcard, ?_⟩
    intro x hx y hy hxy
    have := h x (hts hx) y (hts hy) hxy
    simpa using this

/-- `R(3,3) ≤ 6`. -/
