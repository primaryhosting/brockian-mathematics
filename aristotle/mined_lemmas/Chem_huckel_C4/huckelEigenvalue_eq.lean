/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
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

namespace Chem

open Polynomial

/-- The Hückel (adjacency) matrix of the carbon skeleton of cyclobutadiene `C₄`,
i.e. the adjacency matrix of the cycle graph `C₄`, with coefficients in `R`. -/

theorem huckelEigenvalue_eq (k : Fin 4) : huckelEigenvalue k = ![2, 0, -2, 0] k := by
  unfold huckelEigenvalue
  fin_cases k
  · show (2 : ℝ) * Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) / 4) = 2
    norm_num
  · show (2 : ℝ) * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / 4) = 0
    rw [show (2 * Real.pi * ((1 : ℕ) : ℝ) / 4) = Real.pi / 2 by push_cast; ring]
    simp
  · show (2 : ℝ) * Real.cos (2 * Real.pi * ((2 : ℕ) : ℝ) / 4) = -2
    rw [show (2 * Real.pi * ((2 : ℕ) : ℝ) / 4) = Real.pi by push_cast; ring]
    simp
  · show (2 : ℝ) * Real.cos (2 * Real.pi * ((3 : ℕ) : ℝ) / 4) = 0
    rw [show (2 * Real.pi * ((3 : ℕ) : ℝ) / 4) = Real.pi + Real.pi / 2 by push_cast; ring]
    simp [Real.cos_add]

/-- The product of the linear factors `X - 2cos(2πk/4)` is `X⁴ - 4X²`. -/
