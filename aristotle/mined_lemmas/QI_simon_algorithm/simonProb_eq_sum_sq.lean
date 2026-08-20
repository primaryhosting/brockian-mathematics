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

lemma simonProb_eq_sum_sq {n : ℕ} (f : BV n → BV n) (y : BV n) :
    simonProb f y = ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∑ v : BV n, (ramp f y v) ^ 2 := by
  unfold simonProb
  simp only [simonState_apply, Complex.normSq_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

/-- Key computation: the squared amplitudes sum to `2ⁿ (1 + (-1)^{s·y})`. -/
