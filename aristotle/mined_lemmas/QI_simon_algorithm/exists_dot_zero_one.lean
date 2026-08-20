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

lemma exists_dot_zero_one {n : ℕ} (s t : BV n) (hst : s ≠ t) (ht : t ≠ 0) :
    ∃ v : BV n, dot v s = 0 ∧ dot v t = 1 := by
  classical
  by_cases hex : ∃ k, s k = 0 ∧ t k = 1
  · obtain ⟨k, hk0, hk1⟩ := hex
    exact ⟨basisVec k, by rw [dot_basisVec, hk0], by rw [dot_basisVec, hk1]⟩
  · push_neg at hex
    obtain ⟨b, hb⟩ : ∃ b, t b ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact ht (funext hc)
    have hb1 : t b = 1 := zmod2_eq_one hb
    have hsb : s b = 1 := by
      rcases zmod2_cases (s b) with h | h
      · exact absurd hb1 (hex b h)
      · exact h
    obtain ⟨k, hk⟩ : ∃ k, s k ≠ t k := by
      by_contra hc
      push_neg at hc
      exact hst (funext hc)
    have hsk : s k = 1 := by
      rcases zmod2_cases (s k) with h | h
      · rcases zmod2_cases (t k) with h' | h'
        · exact absurd (h.trans h'.symm) hk
        · exact absurd h' (hex k h)
      · exact h
    have htk : t k = 0 := by
      rcases zmod2_cases (t k) with h | h
      · exact h
      · exact absurd (hsk.trans h.symm) hk
    refine ⟨basisVec b + basisVec k, ?_, ?_⟩
    · rw [dot_add_left, dot_basisVec, dot_basisVec, hsb, hsk]
      decide
    · rw [dot_add_left, dot_basisVec, dot_basisVec, hb1, htk]
      simp

/-- For two distinct nonzero vectors, exactly a quarter of all bit strings are orthogonal to
both. -/
