/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
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

/-- The Hückel (adjacency) matrix of the cycle graph `C₃`: the π-system connectivity
matrix of a three-membered carbon ring, in units where the Coulomb integral is `α = 0`
and the resonance integral is `β = 1`. -/

lemma C3_spectral_prod :
    (∏ k ∈ Finset.range 3, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 3))))
      = X ^ 3 - 3 * X - 2 := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, huckel_val_zero, huckel_val_one, huckel_val_two]
  simp [Polynomial.C_neg, map_ofNat]
  ring

/-- Multiplying a vector by the scalar matrix `μ • 1` is scalar multiplication by `μ`. -/
