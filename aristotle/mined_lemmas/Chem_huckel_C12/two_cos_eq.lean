/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
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

namespace Chem

open Finset Matrix

/-- `zeta a = exp (2πi a / 12)`, the `a`-th power of a primitive 12th root of unity. -/

lemma two_cos_eq (m : ℕ) :
    ((2 * Real.cos (2 * Real.pi * m / 12) : ℝ) : ℂ) = zeta (m : ℤ) + zeta (-(m : ℤ)) := by
  have h : ((2 * Real.cos (2 * Real.pi * m / 12) : ℝ) : ℂ)
      = 2 * Complex.cos ((2 * Real.pi * m / 12 : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_cos]
    ring
  rw [h, Complex.two_cos, zeta, zeta]
  congr 1 <;> · congr 1; push_cast; ring

/-- Multiplying by the adjacency matrix of `C₁₂` adds the two cyclic neighbours. -/
