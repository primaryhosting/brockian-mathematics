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

lemma sqrt_unitary_conj (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (s : n → ℝ) (hs : ∀ i, 0 ≤ s i) :
    CFC.sqrt (U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ)
      = U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Uᴴ := by
  have hUU : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hU
  have ha : (0 : Matrix n n ℂ) ≤ U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ :=
    (posSemidef_unitary_conj U _ (fun i => sq_nonneg (s i))).nonneg
  have hb : (0 : Matrix n n ℂ) ≤ U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Uᴴ :=
    (posSemidef_unitary_conj U s hs).nonneg
  rw [CFC.sqrt_eq_iff _ _ ha hb]
  calc _ = U * diagonal (fun i => ((s i : ℝ) : ℂ)) * (Uᴴ * U) *
              diagonal (fun i => ((s i : ℝ) : ℂ)) * Uᴴ := by noncomm_ring
    _ = U * (diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => ((s i : ℝ) : ℂ))) * Uᴴ := by
        rw [hUU]; noncomm_ring
    _ = U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by rw [diagonal_real_sq]

/-- If `M = U * diagonal s * V` is a singular value decomposition, then
`M * Mᴴ = U * diagonal (s ^ 2) * Uᴴ`. -/
