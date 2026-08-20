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

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- A quantum code, given by the orthogonal projection `P` onto the code subspace. -/
structure IsCodeProj (P : Matrix n n ℂ) : Prop where
  /-- The projection is self-adjoint. -/
  herm : Pᴴ = P
  /-- The projection is idempotent. -/
  idem : P * P = P

/-- The Knill–Laflamme conditions for the code with projection `P` and the error set `E`:
there is a matrix of scalars `c` with `P * (E a)ᴴ * (E b) * P = c a b • P` for all errors
`E a`, `E b`. -/

lemma knillLaflammeCond_of_hasScalarRecovery (P : Matrix n n ℂ) (hP : IsCodeProj P)
    (E : ι → Matrix n n ℂ) (h : HasScalarRecovery P E) : KnillLaflammeCond P E := by
  obtain ⟨m, R, hsum, hl⟩ := h
  choose l hl using hl
  refine ⟨Matrix.of fun a b => ∑ k, (starRingEnd ℂ) (l a k) * l b k, fun a b => ?_⟩
  have expand : ∀ k, (R k * E a * P)ᴴ * (R k * E b * P)
      = (P * (E a)ᴴ) * ((R k)ᴴ * R k) * (E b * P) := by
    intro k
    simp only [conjTranspose_mul, hP.herm]
    noncomm_ring
  have h1 : ∑ k, (R k * E a * P)ᴴ * (R k * E b * P) = P * (E a)ᴴ * E b * P := by
    simp only [expand]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one]
    noncomm_ring
  rw [← h1]
  simp only [hl, conjTranspose_smul, hP.herm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hP.idem, Finset.sum_smul, RCLike.star_def, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- Reindexing a finite Kraus family by `Fin (card κ)`. -/
