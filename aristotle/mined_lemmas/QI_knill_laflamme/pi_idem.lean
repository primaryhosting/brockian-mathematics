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

lemma pi_idem (hP : IsCodeProjector P) (hd : ∀ x, 0 ≤ d x)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P) :
    (∑ x, (recOp P F d x)ᴴ * recOp P F d x) * (∑ x, (recOp P F d x)ᴴ * recOp P F d x)
      = ∑ x, (recOp P F d x)ᴴ * recOp P F d x := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · rw [recOp_conj hP hd, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show F x * P * (F x)ᴴ * (F x * P * (F x)ᴴ) = F x * (P * (F x)ᴴ * F x * P) * (F x)ᴴ by
        noncomm_ring, hFF x x, if_pos rfl, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    rcases eq_or_lt_of_le (hd x) with h0 | h0
    · simp [← h0]
    · have : (d x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h0
      field_simp
  · intro y _ hy
    rw [recOp_conj hP hd, recOp_conj hP hd, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show F x * P * (F x)ᴴ * (F y * P * (F y)ᴴ) = F x * (P * (F x)ᴴ * F y * P) * (F y)ᴴ by
        noncomm_ring, hFF x y, if_neg hy.symm]
    simp
  · intro h; exact absurd (Finset.mem_univ x) h

omit [DecidableEq n] in
/-- The projection `∑ (recOp x)ᴴ (recOp x)` acts as the identity on all error subspaces. -/
