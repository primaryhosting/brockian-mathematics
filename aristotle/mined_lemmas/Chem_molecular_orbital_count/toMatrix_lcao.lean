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

namespace Chem

/-- The LCAO (Linear Combination of Atomic Orbitals) construction: given `n` atomic
orbitals `ao : Fin n → V` and a coefficient matrix `C`, the `i`-th molecular orbital is
`∑ j, C i j • ao j`. -/

lemma toMatrix_lcao {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ao : Module.Basis (Fin n) ℂ V) (C : Matrix (Fin n) (Fin n) ℂ) :
    ao.toMatrix (lcao (⇑ao) C) = C.transpose := by
  ext i j
  simp [Module.Basis.toMatrix_apply, lcao, Matrix.transpose_apply, Finsupp.single_apply,
    Finset.sum_ite_eq']

/-- **LCAO preserves dimension.**  If `n` atomic orbitals form a basis of the orbital space
`V` and the LCAO coefficient matrix `C` is invertible, then the resulting `n` molecular
orbitals are linearly independent and span `V`; in particular they form a basis, so the
number of molecular orbitals equals the number `n` of atomic orbitals, which is the
dimension of `V`. -/
