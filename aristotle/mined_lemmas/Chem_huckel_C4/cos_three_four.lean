/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Chem

open Polynomial

/-- The Hückel matrix of the carbon skeleton of cyclobutadiene, in units where the Coulomb
integral `α` is `0` and the resonance integral `β` is `1`: the adjacency matrix of the cycle
graph `C₄`. -/

lemma cos_three_four : Real.cos (2 * π * (3 : ℕ) / 4) = 0 := by
  have h : (2 * π * (3 : ℕ) / 4 : ℝ) = π + π / 2 := by push_cast; ring
  rw [h, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi]
  ring

/-- The product of the four linear factors `X - 2cos(2πk/4)`. -/
