/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace QI

open Matrix
open scoped Kronecker MatrixOrder

variable {n m : ℕ}

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C = ∑ i j, E i j ⊗ Φ (E i j)`, i.e. `C (i, a) (j, b) = Φ (E i j) a b`. -/

lemma apply_eq_sum_single (X : Matrix (Fin n) (Fin n) ℂ) :
    Φ X = ∑ i, ∑ j, X i j • Φ (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul]
  congr 1
  ext p q
  simp [Matrix.single_apply, Matrix.smul_apply]

/-- The blockwise action of a Kraus family: the ampliation of a map with Kraus operators
`A r` has Kraus operators `1 ⊗ A r`. -/
