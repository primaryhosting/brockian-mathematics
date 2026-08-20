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

/-- The molecular orbitals produced by the LCAO (Linear Combination of Atomic Orbitals)
method: given `n` atomic orbitals `phi j` in a complex vector space of states and a
coefficient matrix `C`, the `i`-th molecular orbital is `∑ j, C i j • phi j`. -/

noncomputable def lcao {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (C : Matrix (Fin n) (Fin n) ℂ) (phi : Fin n → V) : Fin n → V :=
  fun i => ∑ j, C i j • phi j

/-- **LCAO preserves dimension**: `n` linearly independent atomic orbitals `phi`, combined
through an invertible coefficient matrix `C`, yield exactly `n` molecular orbitals.

Formally, the family `lcao C phi` of `n` molecular orbitals is linearly independent, it spans
exactly the same space as the atomic orbitals do, and that space has dimension `n`. Thus no
orbitals are created or destroyed by the linear combination step: `n` atomic orbitals in,
`n` molecular orbitals out. -/
