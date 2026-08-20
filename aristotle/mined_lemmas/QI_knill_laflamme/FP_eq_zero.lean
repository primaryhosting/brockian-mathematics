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

lemma FP_eq_zero (hP : IsCodeProjector P)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P) {x : A}
    (hx : d x = 0) : F x * P = 0 := by
  have key : P * (F x)ᴴ * F x * P = 0 := by simpa [hx] using hFF x x
  refine Matrix.conjTranspose_mul_self_eq_zero.1 ?_
  simp only [Matrix.conjTranspose_mul, hP.herm]
  rw [← mul_assoc]
  exact key

/-- The diagonal Knill–Laflamme coefficients sum to one. -/
