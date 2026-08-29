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

private theorem conj_additiveChar (x : ZMod q) :
    (starRingEnd ℂ) (additiveChar q x) = additiveChar q (-x) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]
  simp [← Circle.coe_inv_eq_conj]

/-- Complex-valued core of Parseval's identity. -/
