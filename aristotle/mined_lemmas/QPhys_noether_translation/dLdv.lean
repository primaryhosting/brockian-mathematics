/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
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

namespace QPhys

/-- The partial derivative `∂L/∂q` of a one-dimensional Lagrangian
`L : position → velocity → time → ℝ`. -/

noncomputable def dLdv (L : ℝ → ℝ → ℝ → ℝ) (q v t : ℝ) : ℝ := deriv (fun w => L q w t) v

/-- **Key lemma.** If the Lagrangian is invariant under spatial translations,
then its partial derivative with respect to position vanishes identically. -/
