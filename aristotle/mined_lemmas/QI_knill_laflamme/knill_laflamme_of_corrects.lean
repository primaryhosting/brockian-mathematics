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

lemma knill_laflamme_of_corrects (P : Matrix n n ℂ) (E : A → Matrix n n ℂ)
    (hP : IsCodeProjector P) (h : Corrects P E) : KnillLaflammeCondition P E := by
  obtain ⟨m, R, hR1, hR2⟩ := h
  -- each operator `R k * E a` acts on the code as a scalar
  have hEig : ∀ (k : Fin m) (a : A), ∃ lam : ℂ, (R k * E a) * P = lam • P := by
    intro k a
    refine exists_const_eigenvalue hP ?_
    intro x hx
    have hrho : P * (vecMulVec x (star x)) * P = vecMulVec x (star x) := by
      rw [show P * vecMulVec x (star x) * P = P * vecMulVec x (star x) * Pᴴ by rw [hP.herm],
        conj_mul_vecMulVec, hx]
    have hsum := hR2 _ hrho
    have hsum2 : ∑ p : Fin m × A,
        vecMulVec ((R p.1 * E p.2) *ᵥ x) (star ((R p.1 * E p.2) *ᵥ x))
        = vecMulVec x (star x) := by
      rw [Fintype.sum_prod_type, ← hsum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
      rw [show R k * E a * vecMulVec x (star x) * (E a)ᴴ * (R k)ᴴ
          = (R k * E a) * vecMulVec x (star x) * (R k * E a)ᴴ by
        simp [Matrix.conjTranspose_mul, mul_assoc]]
      rw [conj_mul_vecMulVec]
    exact exists_smul_of_sum_vecMulVec _ x hsum2 (k, a)
  choose lam hlam using hEig
  refine ⟨fun a b => ∑ k, star (lam k a) * lam k b, fun a b => ?_⟩
  have step : ∀ k : Fin m, (R k * E a * P)ᴴ * (R k * E b * P)
      = (star (lam k a) * lam k b) • P := by
    intro k
    rw [hlam k a, hlam k b, Matrix.conjTranspose_smul, hP.herm, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hP.idem]
  have expand : ∑ k : Fin m, (R k * E a * P)ᴴ * (R k * E b * P)
      = P * (E a)ᴴ * E b * P := by
    rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
      show (R k * E a * P)ᴴ * (R k * E b * P)
        = (P * (E a)ᴴ) * ((R k)ᴴ * R k) * (E b * P) by
          simp only [Matrix.conjTranspose_mul, hP.herm]; noncomm_ring]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hR1, Matrix.mul_one]
    noncomm_ring
  rw [← expand, Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => step k, ← Finset.sum_smul]

/-! ### The converse: the Knill–Laflamme conditions imply correctability

The strategy is the standard one: after diagonalizing the matrix `c` of the Knill–Laflamme
conditions one obtains an equivalent Kraus family `F` for the error channel which satisfies
the *diagonal* Knill–Laflamme conditions `P (F x)ᴴ (F y) P = δₓᵧ dₓ P`.  The recovery channel
is then built out of the partial isometries `P (F x)ᴴ / √dₓ`, completed by the projection onto
the orthogonal complement of the (mutually orthogonal) error subspaces. -/

section Diagonal

variable {P : Matrix n n ℂ} {F : A → Matrix n n ℂ} {d : A → ℝ}

/-- The Kraus operators of the recovery channel attached to a diagonal Knill–Laflamme family. -/
