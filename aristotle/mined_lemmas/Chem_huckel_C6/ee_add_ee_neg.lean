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

lemma ee_add_ee_neg (k : Fin 6) : ee k + ee (-k) = huckelEigenvalue k := by
  have h1 : ee (-k) = (ee k)⁻¹ := (inv_eq_of_mul_eq_one_right (ee_mul_neg k)).symm
  rw [h1, ee_eq_exp, huckelEigenvalue, Complex.ofReal_cos, Complex.cos, ← Complex.exp_neg]
  ring_nf

/-- Multiplication by the adjacency matrix of `C₆` is the discrete "shift-sum". -/
