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

lemma transcript_eq_of_agree {n : ℕ} (A : ClassicalAlg n) (f : BV n → BV n) (m : ℕ)
    (hf : ∀ x ∈ queried A id m, f x = x) :
    ∀ k, k ≤ m → transcript A f k = transcript A id k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hkm : k ≤ m := Nat.le_of_succ_le hk
      have hT : transcript A f k = transcript A id k := ih hkm
      have hq : f (A.query (transcript A id k)) = A.query (transcript A id k) :=
        hf _ (query_mem_queried A id (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk))
      rw [transcript, transcript, hT, hq]
      simp

/-- For `s ≠ 0` there is a canonical choice of representative in each pair `{x, x + s}`. -/
