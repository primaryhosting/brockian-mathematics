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

theorem oscillator_spectrum_fock (hbar omega : ℝ) (hhbar : 0 < hbar) (homega : 0 < omega) :
    {z : ℂ | ∃ v : FockSub, v ≠ 0 ∧ hamiltonian hbar omega annih creat v = z • v}
      = {z : ℂ | ∃ n : ℕ, z = ((hbar * omega * (n + 1 / 2) : ℝ) : ℂ)} :=
  oscillator_spectrum annih creat fock_adj fock_comm vac vac_ne_zero annih_vac
    hbar omega hhbar homega


end

end QPhys

#print axioms QPhys.oscillator_spectrum
#print axioms QPhys.oscillator_spectrum_fock

