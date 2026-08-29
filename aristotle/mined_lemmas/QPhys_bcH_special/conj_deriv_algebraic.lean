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

/-
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- written as an ordinary block comment.)

import Mathlib

/-!
## The special case of the Baker–Campbell–Hausdorff formula

If the commutator `C = A * B - B * A` commutes with both `A` and `B` (in particular if it is
central), then in a Banach algebra
`exp A * exp B = exp (A + B + ½ • (A * B - B * A))`.

Mathlib provides `NormedSpace.exp_add_of_commute` (the case `C = 0`) and the derivative
`hasDerivAt_exp_smul_const`, but not this refinement, so it is proved here by the classical
ODE argument: the function
`t ↦ exp (-(t²/2) • C) * exp (-t • (A+B)) * exp (t • A) * exp (t • B)`
has vanishing derivative, hence is constantly `1`.
-/

open NormedSpace

namespace QPhys

section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

omit [NormedAlgebra ℝ 𝔸] in
/-- Purely algebraic identity used for the derivative of the conjugation `s ↦ e^{-sA} (B + sC) e^{sA}`. -/

theorem conj_deriv_algebraic (u w m A C : 𝔸) (e1 : A * u = u * A) (e2 : A * w = w * A)
    (e3 : A * m = m * A + C) :
    (-(A * u) * m + u * C) * w + u * m * (w * A) = 0 := by
  calc (-(A * u) * m + u * C) * w + u * m * (w * A)
      = u * ((-(A * m) + C) + m * A) * w := by rw [e1, ← e2]; noncomm_ring
    _ = u * ((-(m * A + C) + C) + m * A) * w := by rw [e3]
    _ = 0 := by noncomm_ring

/-- Purely algebraic identity used for the derivative of
`t ↦ e^{-(t²/2)C} e^{-t(A+B)} e^{tA} e^{tB}`. -/
