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

lemma recOp_conj (hP : IsCodeProjector P) (hd : ∀ x, 0 ≤ d x) (x : A) :
    (recOp P F d x)ᴴ * recOp P F d x = ((d x : ℂ))⁻¹ • (F x * P * (F x)ᴴ) := by
  rw [recOp, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hP.herm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show F x * P * (P * (F x)ᴴ) = F x * (P * P) * (F x)ᴴ by noncomm_ring, hP.idem]
  congr 1
  rw [show star ((Real.sqrt (d x) : ℂ))⁻¹ = ((Real.sqrt (d x) : ℂ))⁻¹ by simp]
  exact sqrt_inv_sq _ (hd x)

omit [DecidableEq n] [Fintype A] in
