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
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

/-- A primitive sixth root of unity. -/

lemma ee_eq_exp (k : Fin 6) :
    ee k = Complex.exp (((2 * Real.pi * (k : ℕ) / 6 : ℝ) : ℂ) * Complex.I) := by
  rw [ee, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The adjacency matrix of the cycle graph `C₆`, with vertices indexed by `ℤ/6ℤ`
(realized as `Fin 6`): vertex `i` is adjacent to `i + 1` and to `i - 1`. -/
