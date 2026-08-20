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

def annih : FockSub →ₗ[ℂ] FockSub where
  toFun x := mkFock (annihFun x) (annihFun_finite x)
  map_add' x y := by
    apply Subtype.ext; apply lp.ext; funext n; simp [annihFun]; ring
  map_smul' c x := by
    apply Subtype.ext; apply lp.ext; funext n; simp [annihFun]; ring

/-- The creation operator `a†` on the Fock space. -/
