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

theorem creat_basis (n : ℕ) :
    creat (fockBasis n) = ((Real.sqrt ((n : ℝ) + 1) : ℂ)) • fockBasis (n + 1) := by
  funext m
  cases m with
  | zero => simp [creat, fockBasis]
  | succ k =>
      simp only [creat, fockBasis, LinearMap.coe_mk, AddHom.coe_mk, Nat.add_sub_cancel,
        Pi.smul_apply, smul_eq_mul]
      by_cases h : k = n
      · subst h; simp
      · simp only [Nat.cast_add, Nat.cast_one, if_neg h,
          if_neg (fun hk : k + 1 = n + 1 => h (Nat.succ_injective hk)), mul_zero]

/-- Lowering: `a |n+1⟩ = √(n+1) |n⟩`. -/
