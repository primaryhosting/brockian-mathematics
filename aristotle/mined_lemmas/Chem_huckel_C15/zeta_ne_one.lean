import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
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

open Complex Polynomial Matrix

/-- A primitive 15-th root of unity. -/

lemma zeta_ne_one {d : Fin 15} (hd : d ≠ 0) : zeta d ≠ 1 := by
  intro h
  have hdvd : (15 : ℕ) ∣ (d : ℕ) := (om_isPrimitiveRoot.pow_eq_one_iff_dvd _).mp h
  have h1 : (d : ℕ) < 15 := d.isLt
  have h2 : (d : ℕ) ≠ 0 := fun h0 => hd (Fin.ext h0)
  omega

