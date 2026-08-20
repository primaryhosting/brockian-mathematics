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

lemma ampliation_maxEntangled : ampliation Φ n (maxEntangled n) = choiMatrix Φ := by
  ext x y
  have hblk : (Matrix.of fun p q => maxEntangled n (x.1, p) (y.1, q))
      = Matrix.single x.1 y.1 (1 : ℂ) := by
    ext p q
    simp [maxEntangled, Matrix.single_apply]
    aesop
  simp only [ampliation, choiMatrix, Matrix.of_apply, hblk]

end Aux
/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
