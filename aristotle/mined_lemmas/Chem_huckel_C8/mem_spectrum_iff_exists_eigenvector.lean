import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₈`; this is the Hückel matrix of
cyclooctatetraene in the units where the Coulomb integral is `0` and the resonance
integral is `1`. -/

lemma mem_spectrum_iff_exists_eigenvector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (mu : ℂ) :
    mu ∈ spectrum ℂ M ↔ ∃ v : Fin n → ℂ, v ≠ 0 ∧ M *ᵥ v = mu • v := by
  have hsm : ∀ v : Fin n → ℂ, (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) mu) *ᵥ v = mu • v := by
    intro v
    rw [Algebra.algebraMap_eq_smul_one]
    simp [Matrix.smul_mulVec]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff,
    ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hmv⟩
    rw [sub_mulVec, sub_eq_zero] at hmv
    exact ⟨v, hv, by rw [← hmv, hsm]⟩
  · rintro ⟨v, hv, hmv⟩
    exact ⟨v, hv, by rw [sub_mulVec, sub_eq_zero, hmv, hsm]⟩

