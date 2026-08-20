/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Simon.Defs
import RequestProject.Simon.Quantum
import RequestProject.Simon.Classical
import RequestProject.Simon.Sampling
import RequestProject.Simon.Upper

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
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

namespace QI

open Finset

/-- The measurement outcomes of Simon's circuit form a probability distribution. -/

lemma exists_promise_agreeing {n : ℕ} (X : Finset (BV n)) (s : BV n) (hs : s ≠ 0)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x + y ≠ s) :
    ∃ f : BV n → BV n, SimonPromise f s ∧ ∀ x ∈ X, f x = x := by
  classical
  obtain ⟨c, hc_mem, hc_shift⟩ := exists_canonical_rep s hs
  set f : BV n → BV n := fun x => if x ∈ X then x else if x + s ∈ X then x + s else c x with hf
  have hxx : ∀ x : BV n, x + s + s = x := by
    intro x; rw [add_assoc]; simp
  have hmem : ∀ x : BV n, f x = x ∨ f x = x + s := by
    intro x
    by_cases h1 : x ∈ X
    · exact Or.inl (by simp [hf, h1])
    · by_cases h2 : x + s ∈ X
      · exact Or.inr (by simp [hf, h1, h2])
      · rcases hc_mem x with h | h
        · exact Or.inl (by simp [hf, h1, h2, h])
        · exact Or.inr (by simp [hf, h1, h2, h])
  have hshift : ∀ x : BV n, f (x + s) = f x := by
    intro x
    have hnotboth : ¬ (x ∈ X ∧ x + s ∈ X) := by
      rintro ⟨h1, h2⟩
      have hsum : x + (x + s) = s := by
        rw [← add_assoc]; simp
      exact hX x h1 (x + s) h2 hsum
    simp only [hf]
    rw [hxx x, hc_shift x]
    by_cases h1 : x ∈ X
    · have h2 : x + s ∉ X := fun h2 => hnotboth ⟨h1, h2⟩
      simp [h1, h2]
    · by_cases h2 : x + s ∈ X
      · simp [h1, h2]
      · simp [h1, h2]
  refine ⟨f, ⟨hs, ?_⟩, ?_⟩
  · intro x y
    constructor
    · intro hxy
      rcases hmem x with hx | hx <;> rcases hmem y with hy | hy
      · exact Or.inl (by rw [← hx, ← hy, hxy])
      · refine Or.inr ?_
        have h : x = y + s := by rw [← hx, ← hy, hxy]
        rw [h, hxx]
      · refine Or.inr ?_
        have h : x + s = y := by rw [← hx, ← hy, hxy]
        rw [← h]
      · refine Or.inl ?_
        have h : x + s = y + s := by rw [← hx, ← hy, hxy]
        exact (add_right_cancel h).symm
    · rintro (h | h)
      · rw [h]
      · rw [h, hshift]
  · intro x hx
    simp [hf, hx]

/-- **Classical lower bound (adversary argument).**  If a deterministic classical algorithm
solves Simon's problem with `m` queries then `2ⁿ ≤ m² + 2`. -/
