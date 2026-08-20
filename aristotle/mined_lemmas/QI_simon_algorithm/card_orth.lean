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

lemma card_Orth {n : ℕ} (s : BV n) (hs : s ≠ 0) : 2 * (Orth s).card = 2 ^ n := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, s k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hs (funext hc)
  have hk1 : s k = 1 := zmod2_eq_one hk
  have := card_filter_dot_eq_zero (Finset.univ : Finset (BV n)) (basisVec k) s
    (by intro y; simp) (by rw [dot_basisVec, hk1])
  simpa [Orth, Finset.card_univ] using this

/-- Given `t ≠ 0` and `s ≠ t`, some vector is orthogonal to `s` but not to `t`. -/
