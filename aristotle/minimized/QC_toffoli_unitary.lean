/-
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Equiv

/-- The permutation of the computational basis `|abc⟩` (indexed by `Fin 8` via
`i = 4a + 2b + c`) realized by the Toffoli (CCNOT) gate: it flips the target bit
exactly on the two basis states `|110⟩ = 6` and `|111⟩ = 7`. -/

def toffoliPerm : Equiv.Perm (Fin 8) := Equiv.swap 6 7

/-- The Toffoli (CCNOT) gate as an `8 × 8` complex matrix: the permutation matrix
of `toffoliPerm`. -/

def toffoli : Matrix (Fin 8) (Fin 8) ℂ := toffoliPerm.permMatrix ℂ

/-- The Toffoli matrix in explicit form: the identity on `|000⟩, …, |101⟩`,
and the `X` gate on the last two basis states `|110⟩, |111⟩`. -/

theorem toffoli_mul_self : toffoli * toffoli = 1 := by
  rw [toffoli, ← Matrix.permMatrix_mul]
  simp [toffoliPerm, Equiv.swap_mul_self]

/-- The Toffoli matrix is self-adjoint (it is a real symmetric permutation matrix). -/

theorem toffoli_conjTranspose : toffoliᴴ = toffoli := by
  rw [toffoli, Matrix.conjTranspose_permMatrix]
  simp [toffoliPerm]

/-- **The Toffoli (CCNOT) matrix is unitary.** It is the permutation matrix of the
transposition `(|110⟩ |111⟩)`, hence unitary; moreover it is self-adjoint and equal
to its own inverse. -/

theorem toffoli_unitary : toffoli ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧
    star toffoli = toffoli ∧ toffoli * toffoli = 1 := by
  refine ⟨?_, toffoli_conjTranspose, toffoli_mul_self⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, toffoli_conjTranspose,
    toffoli_mul_self]

end QC

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
