import Mathlib

/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Hamiltonian `ℏω (a† a + ½)` of a one-dimensional quantum harmonic oscillator,
expressed through the annihilation operator `a` and the creation operator `ad = a†`. -/

lemma number_eigenvalue_nonneg (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
    {lam : ℂ} {v : E} (hv : v ≠ 0) (h : ad (a v) = lam • v) :
    ∃ r : ℝ, 0 ≤ r ∧ lam = (r : ℂ) := by
  have key : ⟪a v, a v⟫_ℂ = lam * ⟪v, v⟫_ℂ := by
    rw [hadj v (a v), h, inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at key
  have hvn : (‖v‖ : ℂ) ^ 2 ≠ 0 := by
    simp [pow_eq_zero_iff, norm_eq_zero, hv]
  refine ⟨‖a v‖ ^ 2 / ‖v‖ ^ 2, by positivity, ?_⟩
  push_cast
  rw [eq_div_iff hvn]
  exact key.symm

/-- Lowering: if `v` is an eigenvector of `a†a` with eigenvalue `lam`, then `a v` is an
eigenvector with eigenvalue `lam - 1`. -/
