/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The logarithm of a Hermitian matrix, defined through its spectral decomposition:
if `ρ = U D U*` with `D` the diagonal matrix of eigenvalues, then
`log ρ = U (log D) U*`. -/

theorem eigenvalues_sq_eq_self {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) (hidem : ρ * ρ = ρ) (i : n) :
    h.eigenvalues i * h.eigenvalues i = h.eigenvalues i := by
  set v : n → ℂ := ⇑(h.eigenvectorBasis i) with hv
  set l : ℝ := h.eigenvalues i with hl
  have hmv : ρ *ᵥ v = l • v := h.mulVec_eigenvectorBasis i
  have hvne : v ≠ 0 := (WithLp.ofLp_eq_zero (p := 2)).ne.2 <|
    h.eigenvectorBasis.orthonormal.ne_zero i
  have h1 : ρ *ᵥ (ρ *ᵥ v) = (l * l) • v := by
    rw [hmv, Matrix.mulVec_smul, hmv, smul_smul]
  have h2 : ρ *ᵥ (ρ *ᵥ v) = l • v := by
    rw [Matrix.mulVec_mulVec, hidem, hmv]
  have h3 : (l * l) • v = l • v := by rw [← h1, h2]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hvne
  have h4 : ((l * l : ℝ) : ℂ) * v j = ((l : ℝ) : ℂ) * v j := by
    have := congrFun h3 j
    simpa [Pi.smul_apply, Complex.real_smul] using this
  have := mul_right_cancel₀ hj h4
  exact_mod_cast this

/-- The von Neumann entropy expressed via the eigenvalues: `S(ρ) = -∑ λᵢ log λᵢ`. -/
