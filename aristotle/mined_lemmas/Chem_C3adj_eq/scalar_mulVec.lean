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

lemma scalar_mulVec (μ : ℝ) (v : Fin 3 → ℝ) :
    (Matrix.scalar (Fin 3) μ).mulVec v = μ • v := by
  have h : Matrix.scalar (Fin 3) μ = μ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j; simp [Matrix.scalar, Matrix.one_apply, Matrix.diagonal_apply]
  rw [h, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- `μ` is an eigenvalue of a `3 × 3` real matrix iff `μ • 1 - A` is singular. -/
