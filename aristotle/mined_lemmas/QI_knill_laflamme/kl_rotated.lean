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

lemma kl_rotated (P : Matrix n n ℂ) (E : A → Matrix n n ℂ) (c : A → A → ℂ) (U : Matrix A A ℂ)
    (hc : ∀ a b, P * (E a)ᴴ * E b * P = c a b • P) (x y : A) :
    P * (∑ b, U b x • E b)ᴴ * (∑ b, U b y • E b) * P = ((Uᴴ * (Matrix.of c) * U) x y) • P := by
  have h1 : P * (∑ b, U b x • E b)ᴴ * (∑ b, U b y • E b) * P
      = ∑ b, ∑ b', ((star (U b' x) * (c b' b * U b y)) • P : Matrix n n ℂ) := by
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.mul_sum,
      Matrix.sum_mul]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [show P * (star (U b' x) • (E b')ᴴ) * (U b y • E b) * P
        = (star (U b' x) * U b y) • (P * (E b')ᴴ * E b * P) by
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      congr 1
      ring]
    rw [hc b' b, smul_smul]
    congr 1
    ring
  rw [h1]
  simp only [← Finset.sum_smul]
  congr 1
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b' _ => ?_
  simp [Matrix.conjTranspose_apply]
  ring

omit [DecidableEq n] [Fintype A] [DecidableEq A] in
/-- The matrix of Knill–Laflamme coefficients is Hermitian. -/
