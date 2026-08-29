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

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Polynomial Matrix

/-- The Hückel (adjacency) matrix of the cycle graph `C₆` (the benzene ring), over `ℂ`. -/

lemma two_cos_values (k : Fin 6) :
    2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) = (![2, 1, -1, -2, -1, 1] : Fin 6 → ℝ) k := by
  fin_cases k <;> norm_num
  · rw [show (2 * Real.pi / 6 : ℝ) = Real.pi / 3 by ring, Real.cos_pi_div_three]; norm_num
  · rw [show (2 * Real.pi * 2 / 6 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]; norm_num
  · rw [show (2 * Real.pi * 3 / 6 : ℝ) = Real.pi by ring, Real.cos_pi]; norm_num
  · rw [show (2 * Real.pi * 4 / 6 : ℝ) = 2 * Real.pi - (Real.pi - Real.pi / 3) by ring,
      Real.cos_two_pi_sub, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  · rw [show (2 * Real.pi * 5 / 6 : ℝ) = 2 * Real.pi - Real.pi / 3 by ring, Real.cos_two_pi_sub,
      Real.cos_pi_div_three]; norm_num

