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

lemma svd_mul_conjTranspose {U V : Matrix n n ℂ} (hV : V ∈ Matrix.unitaryGroup n ℂ) (s : n → ℝ) :
    (U * diagonal (fun i => ((s i : ℝ) : ℂ)) * V) *
        (U * diagonal (fun i => ((s i : ℝ) : ℂ)) * V)ᴴ
      = U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
  have hVV : V * Vᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 hV
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, diagonal_real_conjTranspose]
  calc _ = U * (diagonal (fun i => ((s i : ℝ) : ℂ)) * (V * Vᴴ) *
              diagonal (fun i => ((s i : ℝ) : ℂ))) * Uᴴ := by noncomm_ring
    _ = U * (diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => ((s i : ℝ) : ℂ))) * Uᴴ := by
        rw [hVV]; noncomm_ring
    _ = U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by rw [diagonal_real_sq]

/-- Entries of a unitary matrix have norm at most one. -/
