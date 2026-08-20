/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
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

namespace Phys

open Matrix
open scoped ComplexOrder

/-- Von Neumann entropy of a spectrum `p` (a list of eigenvalues of a density matrix). -/

lemma reducedSpectrum_nonneg {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) (a : A) : 0 ≤ reducedSpectrum M a :=
  (Matrix.posSemidef_self_mul_conjTranspose M).eigenvalues_nonneg a

/-- For a normalized state, the reduced spectrum sums to one. -/
