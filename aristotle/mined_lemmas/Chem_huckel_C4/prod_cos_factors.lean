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

lemma prod_cos_factors :
    ∏ k ∈ Finset.range 4, (X - C (2 * Real.cos (2 * π * k / 4)))
      = (X - C 2) * X * (X + C 2) * X := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_succ, Finset.prod_range_zero, cos_zero_four, cos_one_four,
    cos_two_four, cos_three_four]
  norm_num

/-- A real number is an eigenvalue of a matrix (in the sense of admitting a nonzero
eigenvector) exactly when it is a root of the characteristic polynomial. -/
