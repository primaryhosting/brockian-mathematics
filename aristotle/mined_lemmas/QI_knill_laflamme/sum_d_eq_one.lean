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

lemma sum_d_eq_one (hP : IsCodeProjector P)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P)
    (hFsum : ∑ y, (F y)ᴴ * F y = 1) : ∑ y, (d y : ℂ) = 1 := by
  have h1 : ∑ y, P * ((F y)ᴴ * F y) * P = P := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hFsum, Matrix.mul_one, hP.idem]
  have h2 : ∑ y, P * ((F y)ᴴ * F y) * P = (∑ y, (d y : ℂ)) • P := by
    rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) =>
      show P * ((F y)ᴴ * F y) * P = (d y : ℂ) • P by
        rw [← (by simpa using hFF y y : P * (F y)ᴴ * F y * P = (d y : ℂ) • P)]; noncomm_ring,
      ← Finset.sum_smul]
  rw [h2] at h1
  exact smul_eq_smul_of_ne_zero hP.nontrivial (by rw [h1, one_smul])

omit [DecidableEq n] [Fintype A] [DecidableEq A] in
