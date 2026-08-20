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

lemma recFam_recovers (hP : IsCodeProjector P) (hd : ∀ x, 0 ≤ d x)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P)
    (hzero : ∀ x, d x = 0 → F x * P = 0) (hFsum : ∑ y, (F y)ᴴ * F y = 1)
    (rho : Matrix n n ℂ) (hrho : P * rho * P = rho) :
    ∑ k, ∑ y, recFam P F d k * F y * rho * (F y)ᴴ * (recFam P F d k)ᴴ = rho := by
  rw [Fintype.sum_option]
  have hnone : ∑ y, recFam P F d none * F y * rho * (F y)ᴴ * (recFam P F d none)ᴴ = 0 := by
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [sandwich hP _ _ hrho]
    have h0 : recFam P F d none * F y * P = 0 := by
      show (1 - ∑ x, (recOp P F d x)ᴴ * recOp P F d x) * F y * P = 0
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, mul_assoc, pi_mul hP hd hFF hzero y,
        sub_self]
    rw [h0]
    simp
  have hsome : ∀ x : A, ∑ y, recFam P F d (some x) * F y * rho * (F y)ᴴ
      * (recFam P F d (some x))ᴴ = (d x : ℂ) • rho := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [sandwich hP _ _ hrho]
      show (recOp P F d x * F x * P) * rho * (recOp P F d x * F x * P)ᴴ = _
      rw [recOp_mul hd hFF, if_pos rfl, Matrix.conjTranspose_smul, hP.herm, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_mul, smul_smul, hrho,
        show star ((Real.sqrt (d x) : ℝ) : ℂ) = ((Real.sqrt (d x) : ℝ) : ℂ) by simp]
      congr 1
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd x)]
    · intro y _ hy
      rw [sandwich hP _ _ hrho]
      show (recOp P F d x * F y * P) * rho * (recOp P F d x * F y * P)ᴴ = _
      rw [recOp_mul hd hFF, if_neg hy.symm]
      simp
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [hnone, zero_add, Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hsome x,
    ← Finset.sum_smul, sum_d_eq_one hP hFF hFsum, one_smul]

end Diagonal

/-! ### Diagonalizing the Knill–Laflamme matrix -/

omit [Fintype n] [DecidableEq n] in
