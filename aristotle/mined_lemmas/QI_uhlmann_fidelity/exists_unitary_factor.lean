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

lemma exists_unitary_factor {A ρ : Matrix n n ℂ} (h : A * Aᴴ = ρ) :
    ∃ V ∈ Matrix.unitaryGroup n ℂ, A = CFC.sqrt ρ * V := by
  obtain ⟨U, V', s, hs, hU, hV', hA⟩ := exists_svd A
  have hUU : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hU
  have hrho : ρ = U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [← h, hA, svd_mul_conjTranspose hV' s]
  refine ⟨U * V', (Matrix.unitaryGroup n ℂ).mul_mem hU hV', ?_⟩
  rw [hrho, sqrt_unitary_conj U hU s hs, hA]
  calc _ = U * diagonal (fun i => ((s i : ℝ) : ℂ)) * (Uᴴ * U) * V' := by rw [hUU]; noncomm_ring
    _ = U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Uᴴ * (U * V') := by noncomm_ring

/-! ## Fidelity and purifications -/

/-- The (Uhlmann) fidelity of two positive semidefinite matrices,
`F(ρ, σ) = tr √(√ρ σ √ρ)`. -/
