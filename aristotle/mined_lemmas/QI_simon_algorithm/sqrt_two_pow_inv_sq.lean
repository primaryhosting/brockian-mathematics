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

lemma sqrt_two_pow_inv_sq (n : ℕ) :
    ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹
      = (((2 : ℝ) ^ n : ℝ) : ℂ)⁻¹ := by
  have h : Real.sqrt ((2:ℝ) ^ n) * Real.sqrt ((2:ℝ) ^ n) = (2:ℝ) ^ n :=
    Real.mul_self_sqrt (by positivity)
  have h2 : ((Real.sqrt ((2:ℝ) ^ n) : ℝ) : ℂ) * ((Real.sqrt ((2:ℝ) ^ n) : ℝ) : ℂ)
      = (((2:ℝ) ^ n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, h]
  rw [← mul_inv, h2]

/-- The (real) amplitude, up to the normalisation factor `2⁻ⁿ`, of the basis state `|y⟩|v⟩`
at the end of Simon's circuit. -/
