import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
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

set_option grind.warning false

namespace Chem

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/

lemma F_isUnit_det : IsUnit F.det := by
  rw [F_eq_vandermonde]
  refine isUnit_iff_ne_zero.mpr ?_
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  have := w_isPrimitiveRoot.pow_inj a.isLt b.isLt hab
  exact Fin.ext this

/-- The eigenvalue identity `ω^k + ω^{19k} = 2 cos(2πk/20)`. -/
