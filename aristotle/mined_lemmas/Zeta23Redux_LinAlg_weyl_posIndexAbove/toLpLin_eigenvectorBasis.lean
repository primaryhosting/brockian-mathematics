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
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix Finset

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

lemma toLpLin_eigenvectorBasis {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (j : Fin d) :
    Matrix.toLpLin 2 2 A (hA.eigenvectorBasis j)
      = (hA.eigenvalues j : ℂ) • hA.eigenvectorBasis j := by
  ext k
  simp [Matrix.toLpLin_apply, hA.mulVec_eigenvectorBasis j, Complex.real_smul]

