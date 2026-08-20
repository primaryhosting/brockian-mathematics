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

/-! ## The Fock space of the harmonic oscillator

We model the oscillator on the Fock (occupation-number) space: a state is a family of
complex amplitudes indexed by the occupation number `n : ℕ`, i.e. an element of `ℕ → ℂ`.
The `n`-th basis state `fockBasis n` is the state with a single unit amplitude at level `n`.
-/

/-- States of the harmonic oscillator, described by their amplitudes in the number basis. -/
abbrev Fock := ℕ → ℂ

/-- The `n`-th number eigenstate `|n⟩`. -/

theorem creat_pow_ground (n : ℕ) :
    (creat ^ n) (fockBasis 0) = ((Real.sqrt (n ! : ℝ) : ℂ)) • fockBasis n := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, creat_basis, smul_smul,
        ← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
      congr 2
      rw [Nat.factorial_succ]
      push_cast
      rw [mul_comm]

/-- Each number state is an eigenstate of the Hamiltonian with energy `ℏω(n + 1/2)`. -/
