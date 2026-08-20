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

lemma fock_comm (x : FockSub) : annih (creat x) - creat (annih x) = x := by
  apply Subtype.ext; apply lp.ext; funext n
  match n with
  | 0 => simp
  | (m + 1) =>
      simp only [AddSubgroupClass.coe_sub, Pi.sub_apply, annih_apply, creat_apply_succ]
      ring_nf
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), ← Complex.ofReal_pow,
        Real.sq_sqrt (by positivity)]
      push_cast
      ring

/-- `a†` is the adjoint of `a` on the Fock space. -/
