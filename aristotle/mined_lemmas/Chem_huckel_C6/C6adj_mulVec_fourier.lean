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

theorem C6adj_mulVec_fourier (k : Fin 6) :
    C6adj.mulVec (fun x => ee (k * x)) = huckelEigenvalue k • (fun x => ee (k * x)) := by
  funext x
  rw [C6adj_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, ← ee_add_ee_neg]
  have h1 : k * (x + 1) = k * x + k := by rw [mul_add, mul_one]
  have h2 : k * (x - 1) = k * x + (-k) := by rw [mul_sub, mul_one, sub_eq_add_neg]
  rw [h1, h2, ee_add, ee_add]
  ring

/-- The Fourier (Vandermonde) matrix diagonalizing the adjacency matrix of `C₆`. -/
