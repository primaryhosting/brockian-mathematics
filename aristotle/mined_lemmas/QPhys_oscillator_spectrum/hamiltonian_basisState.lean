/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

/-- The state space of the quantum harmonic oscillator, in the occupation-number
(Fock) representation: a state is described by its sequence of coefficients in the
number basis. -/
abbrev Fock : Type := ℕ → ℂ

/-- The `n`-th number-basis state `|n⟩`. -/

lemma hamiltonian_basisState (hbar omega : ℝ) (n : ℕ) :
    hamiltonian hbar omega (basisState n)
      = (((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2)) • basisState n := by
  funext m
  rw [hamiltonian_apply]
  by_cases h : m = n
  · subst h; simp [basisState]
  · simp [basisState, h]

end Basic

/-- **Spectrum of the quantum harmonic oscillator.**
For the Hamiltonian `H = ℏω (a†a + 1/2)` built from the ladder operators `a`, `a†`
acting on the Fock space of occupation-number sequences, the set of eigenvalues of
`H` is exactly `{ℏω(n + 1/2) : n ∈ ℕ}`. -/
