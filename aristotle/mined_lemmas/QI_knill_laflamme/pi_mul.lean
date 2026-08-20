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

lemma pi_mul (hP : IsCodeProjector P) (hd : ∀ x, 0 ≤ d x)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P)
    (hzero : ∀ x, d x = 0 → F x * P = 0) (y : A) :
    (∑ x, (recOp P F d x)ᴴ * recOp P F d x) * (F y * P) = F y * P := by
  rw [Finset.sum_mul, Finset.sum_eq_single y]
  · rw [recOp_conj hP hd, Matrix.smul_mul,
      show F y * P * (F y)ᴴ * (F y * P) = F y * (P * (F y)ᴴ * F y * P) by noncomm_ring,
      hFF y y, if_pos rfl, Matrix.mul_smul, smul_smul]
    rcases eq_or_lt_of_le (hd y) with h0 | h0
    · rw [hzero y h0.symm]
      simp
    · have : (d y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h0
      rw [inv_mul_cancel₀ this, one_smul]
  · intro x _ hx
    rw [recOp_conj hP hd, Matrix.smul_mul,
      show F x * P * (F x)ᴴ * (F y * P) = F x * (P * (F x)ᴴ * F y * P) by noncomm_ring,
      hFF x y, if_neg hx]
    simp
  · intro h; exact absurd (Finset.mem_univ y) h

omit [DecidableEq n] in
