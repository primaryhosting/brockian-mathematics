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

lemma sum_unitary_comb (U : Matrix A A ℂ) (hU : U * Uᴴ = 1) (G : A → A → Matrix n n ℂ) :
    ∑ y, ∑ b, ∑ b', ((U b y * star (U b' y)) • G b b') = ∑ b, G b b := by
  have step1 : ∑ y, ∑ b, ∑ b', ((U b y * star (U b' y)) • G b b')
      = ∑ b, ∑ b', (∑ y, (U b y * star (U b' y))) • G b b' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [← Finset.sum_smul]
  rw [step1]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single b]
  · have h : ∑ y, U b y * star (U b y) = 1 := by
      have := congrFun (congrFun hU b) b
      rw [Matrix.mul_apply] at this
      simpa [Matrix.conjTranspose_apply] using this
    rw [h, one_smul]
  · intro b' _ hb'
    have h : ∑ y, U b y * star (U b' y) = 0 := by
      have := congrFun (congrFun hU b) b'
      rw [Matrix.mul_apply] at this
      simpa [Matrix.conjTranspose_apply, Matrix.one_apply, Ne.symm hb'] using this
    rw [h, zero_smul]
  · intro h; exact absurd (Finset.mem_univ b) h

omit [DecidableEq n] in
/-- Two Kraus families related by a unitary matrix define the same channel. -/
