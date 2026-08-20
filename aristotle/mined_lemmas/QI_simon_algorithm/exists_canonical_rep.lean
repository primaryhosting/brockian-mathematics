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

lemma exists_canonical_rep {n : ℕ} (s : BV n) (hs : s ≠ 0) :
    ∃ c : BV n → BV n, (∀ x, c x = x ∨ c x = x + s) ∧ (∀ x, c (x + s) = c x) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, s k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hs (funext hc)
  have hk1 : s k = 1 := zmod2_eq_one hk
  refine ⟨fun x => if x k = 0 then x else x + s, ?_, ?_⟩
  · intro x
    by_cases h : x k = 0
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
  · intro x
    have hxx : x + s + s = x := by
      rw [add_assoc]; simp
    by_cases h : x k = 0
    · have h1 : (x + s) k = 1 := by simp [h, hk1]
      have h1' : ¬ ((x + s) k = 0) := by rw [h1]; exact one_ne_zero
      simp only [if_neg h1', if_pos h, hxx]
    · have hx1 : x k = 1 := zmod2_eq_one h
      have h0 : (x + s) k = 0 := by
        show x k + s k = 0
        rw [hx1, hk1]
        decide
      simp only [if_pos h0, if_neg h]

/-- The adversary's family of instances: for every `s` that is not a sum of two queried
points, there is an oracle satisfying Simon's promise with period `s` that answers all queried
points by the identity. -/
