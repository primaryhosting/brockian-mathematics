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

lemma lower_ne_zero (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
    {lam : ℂ} {v : E} (hv : v ≠ 0) (hlam : lam ≠ 0) (h : ad (a v) = lam • v) :
    a v ≠ 0 := by
  intro hav
  have key : ⟪a v, a v⟫_ℂ = lam * ⟪v, v⟫_ℂ := by
    rw [hadj v (a v), h, inner_smul_right]
  rw [hav] at key
  simp only [inner_zero_left] at key
  rcases mul_eq_zero.mp key.symm with h1 | h1
  · exact hlam h1
  · exact hv (by simpa [inner_self_eq_zero] using h1)

/-- Ladder descent: any eigenvalue of the number operator is a natural number. -/
