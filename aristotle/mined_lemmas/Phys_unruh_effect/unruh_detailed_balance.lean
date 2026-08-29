/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the mandated
-- header above is written as an ordinary block comment; its text is unchanged.)

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

namespace Phys

/-! ## Definitions -/

/-- The **Unruh temperature** `T = ℏ a / (2 π c k_B)` associated with proper acceleration `a`. -/

theorem unruh_detailed_balance (hbar a c kB : ℝ) (hbar0 : hbar ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hk : kB ≠ 0) (ω : ℝ) :
    Real.exp (-(2 * Real.pi * c * ω / a))
      = Real.exp (-(hbar * ω / (kB * unruhTemp hbar a c kB))) := by
  congr 1
  have h := unruh_beta hbar a c kB hbar0 ha hc hk
  have hsplit : hbar * ω / (kB * unruhTemp hbar a c kB)
      = (hbar / (kB * unruhTemp hbar a c kB)) * ω := by ring
  rw [hsplit, h]
  ring

/-- A mode whose emission/absorption rates satisfy detailed balance at temperature `T`
has the Planck (Bose–Einstein) mean occupation number at that temperature. -/
