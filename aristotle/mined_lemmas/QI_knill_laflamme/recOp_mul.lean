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

lemma recOp_mul (hd : ∀ x, 0 ≤ d x)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P) (x y : A) :
    recOp P F d x * F y * P = (if x = y then ((Real.sqrt (d x) : ℝ) : ℂ) else 0) • P := by
  rw [recOp, Matrix.smul_mul, Matrix.smul_mul, show P * (F x)ᴴ * F y * P
    = (if x = y then (d x : ℂ) else 0) • P from hFF x y, smul_smul]
  congr 1
  by_cases h : x = y
  · simp only [if_pos h]
    exact sqrt_inv_mul _ (hd x)
  · simp [h]

omit [DecidableEq n] in
/-- The sum `∑ (recOp x)ᴴ (recOp x)` is an orthogonal projection. -/
