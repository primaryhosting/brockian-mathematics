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

lemma kl_isHermitian {P : Matrix n n ℂ} {E : A → Matrix n n ℂ} {c : A → A → ℂ}
    (hP : IsCodeProjector P) (hc : ∀ a b, P * (E a)ᴴ * E b * P = c a b • P) :
    (Matrix.of c).IsHermitian := by
  ext a b
  have h1 : (P * (E b)ᴴ * E a * P)ᴴ = P * (E a)ᴴ * E b * P := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP.herm]
    noncomm_ring
  rw [hc b a, hc a b, Matrix.conjTranspose_smul, hP.herm] at h1
  exact smul_eq_smul_of_ne_zero hP.nontrivial h1

omit [DecidableEq A] in
/-- Any recovery family can be re-indexed by `Fin m`. -/
