import Mathlib
/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Singular value decomposition -/

/-- Every square complex matrix admits a singular value decomposition
`M = U * diagonal s * V` with `U`, `V` unitary and `s` a nonnegative real vector. -/

lemma posSemidef_unitary_conj (U : Matrix n n ℂ) (s : n → ℝ) (hs : ∀ i, 0 ≤ s i) :
    (U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Uᴴ).PosSemidef := by
  have h : U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Uᴴ
      = (U * diagonal (fun i => ((Real.sqrt (s i) : ℝ) : ℂ))) *
        (U * diagonal (fun i => ((Real.sqrt (s i) : ℝ) : ℂ)))ᴴ := by
    rw [Matrix.conjTranspose_mul, diagonal_real_conjTranspose]
    simp only [Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hs i)]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- The positive semidefinite square root of `U * diagonal (s ^ 2) * Uᴴ`. -/
