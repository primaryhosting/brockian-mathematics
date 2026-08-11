/-!
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Statement: The Toffoli (CCNOT) matrix is a permutation matrix hence unitary and its own inverse.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

open Matrix

/-- The eight classical basis states of a three-qubit register. -/
abbrev Q3 : Type := Fin 2 × Fin 2 × Fin 2

/-- The Toffoli (CCNOT) action on classical basis states: the third (target) bit is
flipped exactly when both control bits are `1`. -/
def toffoliMap (p : Q3) : Q3 :=
  (p.1, p.2.1, if p.1 = 1 ∧ p.2.1 = 1 then p.2.2 + 1 else p.2.2)

/-- The Toffoli action is an involution of the basis states. -/
theorem toffoliMap_involutive : Function.Involutive toffoliMap := by
  intro x; revert x; decide

theorem toffoliMap_eq_iff (i j : Q3) : toffoliMap i = j ↔ i = toffoliMap j :=
  ⟨fun h => h ▸ (toffoliMap_involutive i).symm, fun h => h ▸ toffoliMap_involutive j⟩

/-- The Toffoli gate as a permutation of the eight classical basis states. -/
def toffoliPerm : Equiv.Perm Q3 := toffoliMap_involutive.toPerm _

@[simp] theorem toffoliPerm_apply (p : Q3) : toffoliPerm p = toffoliMap p := rfl

/-- The Toffoli (CCNOT) matrix, acting on `ℂ`-valued three-qubit states:
`toffoli i j = 1` exactly when the basis state `j` is mapped to the basis state `i`. -/
def toffoli : Matrix Q3 Q3 ℂ := Matrix.of fun i j => if i = toffoliMap j then 1 else 0

/-- The Toffoli matrix is the permutation matrix of `toffoliPerm`. -/
theorem toffoli_eq_permMatrix : toffoli = toffoliPerm.permMatrix ℂ := by
  ext i j
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  show (if i = toffoliMap j then (1 : ℂ) else 0) = _
  simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, toffoliPerm_apply]
  simp only [toffoliMap_eq_iff]

/-- The Toffoli matrix is symmetric under conjugate transpose. -/
theorem toffoli_conjTranspose : toffoliᴴ = toffoli := by
  ext i j
  have h : (j = toffoliMap i) ↔ (i = toffoliMap j) := by
    rw [← toffoliMap_eq_iff, eq_comm]
  simp only [Matrix.conjTranspose_apply, toffoli, Matrix.of_apply, h]
  split <;> simp

/-- The Toffoli gate is its own inverse. -/
theorem toffoli_mul_self : toffoli * toffoli = 1 := by
  ext i k
  rw [Matrix.mul_apply, Finset.sum_eq_single (toffoliMap k)]
  · simp [toffoli, Matrix.one_apply, toffoliMap_involutive k]
  · intro b _ hb
    simp [toffoli, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The Toffoli (CCNOT) matrix is a permutation matrix, hence unitary, and it is its
own inverse.** -/
theorem toffoli_unitary :
    toffoli = toffoliPerm.permMatrix ℂ ∧
      toffoli ∈ Matrix.unitaryGroup Q3 ℂ ∧
      toffoliᴴ * toffoli = 1 ∧ toffoli * toffoliᴴ = 1 ∧
      toffoli * toffoli = 1 := by
  have hH : toffoliᴴ * toffoli = 1 := by
    rw [toffoli_conjTranspose]; exact toffoli_mul_self
  have hH' : toffoli * toffoliᴴ = 1 := by
    rw [toffoli_conjTranspose]; exact toffoli_mul_self
  refine ⟨toffoli_eq_permMatrix, ?_, hH, hH', toffoli_mul_self⟩
  rw [Matrix.mem_unitaryGroup_iff']
  exact hH

end QC

