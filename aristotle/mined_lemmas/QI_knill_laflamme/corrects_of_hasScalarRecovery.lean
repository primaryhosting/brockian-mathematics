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

lemma corrects_of_hasScalarRecovery (P : Matrix n n ℂ) (hP : IsCodeProj P)
    (E : ι → Matrix n n ℂ) (h : HasScalarRecovery P E) : CorrectsErrorSet P E := by
  obtain ⟨m, R, hsum, hl⟩ := h
  choose l hl using hl
  refine ⟨m, R, hsum, fun a => ⟨∑ k, l a k * (starRingEnd ℂ) (l a k), fun ρ hρ => ?_⟩⟩
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hstar : P * (E a)ᴴ * (R k)ᴴ = (starRingEnd ℂ) (l a k) • P := by
    have h2 : (R k * E a * P)ᴴ = (l a k • P)ᴴ := by rw [hl a k]
    simpa [conjTranspose_mul, hP.herm, mul_assoc] using h2
  calc R k * (E a * ρ * (E a)ᴴ) * (R k)ᴴ
      = (R k * E a * P) * ρ * (P * (E a)ᴴ * (R k)ᴴ) := by
        conv_lhs => rw [← hρ]
        noncomm_ring
    _ = (l a k • P) * ρ * ((starRingEnd ℂ) (l a k) • P) := by rw [hl a k, hstar]
    _ = (l a k * (starRingEnd ℂ) (l a k)) • ρ := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hρ]
        rw [mul_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- Conversely, a recovery channel restoring all code states must act as a scalar on the code. -/
