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

/-- Computational basis states of three qubits. -/
abbrev Q3 := Bool × Bool × Bool

/-- The classical action of the Toffoli (CCNOT) gate on basis states: the third bit is
negated exactly when the first two bits are both `true`. -/
def toffoliMap : Q3 → Q3 := fun x => (x.1, x.2.1, xor (x.1 && x.2.1) x.2.2)

/-- The Toffoli action is an involution. -/
theorem toffoliMap_involutive : Function.Involutive toffoliMap := by decide

/-- The Toffoli permutation of the three-qubit basis states. -/
def toffoliPerm : Equiv.Perm Q3 := Function.Involutive.toPerm _ toffoliMap_involutive

/-- The Toffoli (CCNOT) matrix: the permutation matrix of `toffoliMap`. -/
def toffoli : Matrix Q3 Q3 ℂ := Matrix.of fun i j => if j = toffoliMap i then 1 else 0

theorem toffoli_apply (i j : Q3) : toffoli i j = if j = toffoliMap i then 1 else 0 := rfl

/-- Each entry of the Toffoli matrix is `0` or `1`. -/
theorem toffoli_entry_zero_or_one (i j : Q3) : toffoli i j = 0 ∨ toffoli i j = 1 := by
  rw [toffoli_apply]; split <;> simp

/-- The Toffoli matrix is symmetric, since `toffoliMap` is an involution. -/
theorem toffoli_transpose : toffoliᵀ = toffoli := by
  ext i j
  simp only [Matrix.transpose_apply, toffoli_apply]
  by_cases h : j = toffoliMap i
  · subst h
    simp [toffoliMap_involutive j]
  · have h' : i ≠ toffoliMap j := by
      intro hij
      exact h (by rw [hij, toffoliMap_involutive j])
    simp [h, h']

/-- The Toffoli matrix has real entries, so it equals its conjugate transpose. -/
theorem toffoli_conjTranspose : toffoliᴴ = toffoli := by
  ext i j
  rw [Matrix.conjTranspose_apply, ← Matrix.transpose_apply, toffoli_transpose, toffoli_apply]
  split <;> simp

/-- The Toffoli matrix is its own inverse: `T * T = 1`. -/
theorem toffoli_mul_self : toffoli * toffoli = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (toffoliMap i)]
  · simp only [toffoli_apply, if_pos rfl, one_mul, toffoliMap_involutive i,
      Matrix.one_apply]
    by_cases h : k = i
    · simp [h]
    · simp [h, fun hh : k = i => h hh, Ne.symm h]
  · intro b _ hb
    simp [toffoli_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The Toffoli (CCNOT) gate is a unitary matrix which is its own inverse.**
It is the permutation matrix of the involutive permutation `toffoliMap` of the eight
three-qubit computational basis states, all of its entries are `0` or `1`, it is
self-adjoint, and `T * T = 1`. -/
theorem toffoli_unitary :
    (∀ i j, toffoli i j = 0 ∨ toffoli i j = 1) ∧
    toffoliᴴ = toffoli ∧
    toffoli * toffoli = 1 ∧
    toffoli ∈ Matrix.unitaryGroup Q3 ℂ := by
  refine ⟨toffoli_entry_zero_or_one, toffoli_conjTranspose, toffoli_mul_self, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  rw [toffoli_conjTranspose, toffoli_mul_self]

end QC

