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

lemma number_lower (hcomm : ∀ x : E, a (ad x) - ad (a x) = x)
    {lam : ℂ} {v : E} (h : ad (a v) = lam • v) :
    ad (a (a v)) = (lam - 1) • (a v) := by
  have h1 := hcomm (a v)
  have h2 : a (ad (a v)) = lam • a v := by rw [h, map_smul]
  have : ad (a (a v)) = a (ad (a v)) - a v := by
    linear_combination (norm := module) -h1
  rw [this, h2]
  module

