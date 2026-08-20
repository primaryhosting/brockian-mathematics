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

lemma annihFun_finite (x : FockSub) : {n | annihFun x n ≠ 0}.Finite := by
  refine Set.Finite.subset (Set.Finite.preimage (f := fun n : ℕ => n + 1) ?_ (fock_finite x)) ?_
  · exact Set.injOn_of_injective (fun p q h => by omega)
  · intro n hn
    simp only [Set.mem_setOf_eq, annihFun] at hn
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    intro h; simp [h] at hn

