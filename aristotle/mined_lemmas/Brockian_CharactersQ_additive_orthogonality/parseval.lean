import Mathlib

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

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Tactic

/-!
# Fourier analysis and characters on `ZMod q`

The reusable, general-modulus character kernel needed by the analytic large-sieve and
Bombieri--Vinogradov layers.  This module deliberately wraps Mathlib's canonical
`ZMod.stdAddChar`, `ZMod.dft`, and `DirichletCharacter`; it introduces no competing
character convention.
-/

open scoped BigOperators

noncomputable section

namespace Brockian.CharactersQ

variable (q : ℕ) [NeZero q]

/-- Mathlib's canonical additive character `x ↦ exp (2πix/q)`. -/
abbrev additiveChar : AddChar (ZMod q) ℂ := ZMod.stdAddChar

/-- Complex Dirichlet characters modulo `q`, reused from Mathlib. -/
abbrev MultiplicativeChar := DirichletCharacter ℂ q

/-- The unnormalised discrete Fourier transform on `ZMod q`. -/

theorem parseval (f : ZMod q → ℂ) :
    ∑ a : ZMod q, ‖fourier q f a‖ ^ 2 =
      q * ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have h := parseval_core q f
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have hcast :
      (((∑ a : ZMod q, ‖fourier q f a‖ ^ 2 : ℝ)) : ℂ) =
        (((q * ∑ x : ZMod q, ‖f x‖ ^ 2 : ℝ)) : ℂ) := by
    push_cast
    push_cast at h
    exact h
  exact_mod_cast hcast

/-- A nontrivial complex Dirichlet character has zero complete sum. -/
