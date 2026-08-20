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

lemma d_nonneg (hP : IsCodeProjector P)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P) (x : A) :
    0 ≤ d x := by
  obtain ⟨psi, hpsi, hpsine⟩ := exists_ne_zero_mem_code hP
  have hps : ((F x * P)ᴴ * (F x * P)).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have heq : (F x * P)ᴴ * (F x * P) = (d x : ℂ) • P := by
    rw [Matrix.conjTranspose_mul, hP.herm,
      ← (by simpa using hFF x x : P * (F x)ᴴ * F x * P = (d x : ℂ) • P)]
    noncomm_ring
  rw [heq] at hps
  have h2 := hps.dotProduct_mulVec_nonneg psi
  rw [Matrix.smul_mulVec, hpsi, dotProduct_smul, smul_eq_mul] at h2
  have hpos : (0 : ℂ) < star psi ⬝ᵥ psi := dotProduct_star_self_pos_iff.2 hpsine
  simp only [Complex.le_def, Complex.lt_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, Complex.zero_im, zero_mul, sub_zero, add_zero] at h2 hpos
  nlinarith [h2.1, hpos.1]

omit [DecidableEq n] [Fintype A] in
/-- An error with vanishing coefficient annihilates the code. -/
