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

lemma inner_ad_left (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ) (x y : E) :
    ⟪ad x, y⟫_ℂ = ⟪x, a y⟫_ℂ := by
  rw [← inner_conj_symm (𝕜 := ℂ) (ad x) y, ← hadj, inner_conj_symm]

/-- `a†a` acting on an `n`-fold excited state. -/
