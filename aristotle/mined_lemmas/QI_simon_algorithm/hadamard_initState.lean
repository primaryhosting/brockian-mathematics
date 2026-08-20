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

lemma hadamard_initState {n : ℕ} (x v : BV n) :
    hadamardFirst (initState n) x v
      = ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * (if v = 0 then 1 else 0) := by
  classical
  unfold hadamardFirst initState
  congr 1
  rw [Finset.sum_eq_single (0 : BV n)]
  · by_cases hv : v = 0 <;> simp [hv]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (0 : BV n)) h

