/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n A : Type*} [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A]

/-- A *code* is given by the orthogonal projection `P` onto the code subspace: `P` is
self-adjoint, idempotent, and nonzero (the code subspace is nontrivial). -/
structure IsCodeProjector (P : Matrix n n ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  nontrivial : P ≠ 0

/-- The error set `E` is the Kraus family of a quantum channel (trace preserving). -/

lemma sqrt_inv_mul (dx : ℝ) (h : 0 ≤ dx) :
    ((Real.sqrt dx : ℂ))⁻¹ * (dx : ℂ) = (Real.sqrt dx : ℂ) := by
  rcases eq_or_lt_of_le h with h0 | h0
  · simp [← h0]
  · have hs : (Real.sqrt dx : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.2 h0)
    have hsq : (Real.sqrt dx : ℂ) * (Real.sqrt dx : ℂ) = (dx : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt h]
    field_simp
    rw [pow_two, hsq]

