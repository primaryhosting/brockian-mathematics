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

lemma recFam_sum_one (hP : IsCodeProjector P) (hd : ∀ x, 0 ≤ d x)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P) :
    ∑ k, (recFam P F d k)ᴴ * recFam P F d k = 1 := by
  set Pi : Matrix n n ℂ := ∑ x, (recOp P F d x)ᴴ * recOp P F d x with hPi
  have hherm : Piᴴ = Pi := by
    rw [hPi]
    simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul]
  rw [Fintype.sum_option]
  show (1 - Pi)ᴴ * (1 - Pi) + ∑ x, (recOp P F d x)ᴴ * recOp P F d x = 1
  rw [← hPi, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hherm,
    show (1 - Pi) * (1 - Pi) = 1 - Pi - Pi + Pi * Pi by noncomm_ring, pi_idem hP hd hFF, ← hPi]
  noncomm_ring

/-- The recovery family undoes the error channel given in diagonal form. -/
