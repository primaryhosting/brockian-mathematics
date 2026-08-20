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

theorem simonProb_eq {n : ℕ} {f : BV n → BV n} {s : BV n} (h : SimonPromise f s) (y : BV n) :
    simonProb f y = if dot s y = 0 then 2 / 2 ^ n else 0 := by
  rw [simonProb_eq_sum_sq, sum_ramp_sq h y]
  by_cases hy : dot s y = 0
  · rw [if_pos hy, hy, rsgn_zero]
    have h2 : ((2:ℝ) ^ n) ≠ 0 := by positivity
    field_simp
    ring
  · rw [if_neg hy, rsgn, if_neg hy]
    ring

end QI

import Mathlib

/-!
# Simon's problem: basic definitions

We model `n`-bit strings as vectors over the two-element field `ZMod 2`.
-/

namespace QI

open Finset

/-- `n`-bit strings, viewed as vectors over `𝔽₂`. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

/-- The standard `𝔽₂`-bilinear form ("inner product mod 2") on bit strings. -/
