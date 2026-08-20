/-
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- The Toffoli (CCNOT) gate as an `8 × 8` complex matrix, in the standard
computational basis ordering `|a b c⟩ ↦ 4a + 2b + c`.  It is the identity except
that it swaps the basis states `|110⟩` and `|111⟩`. -/
def toffoli : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1,0,0,0,0,0,0,0;
     0,1,0,0,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,0,0,0,0,0,0,1;
     0,0,0,0,0,0,1,0]

/-- Index of the computational basis state `|a b c⟩`. -/
def bitIdx (a b c : Fin 2) : Fin 8 :=
  ⟨4 * a.val + 2 * b.val + c.val, by omega⟩

/-- The Toffoli matrix implements the classical CCNOT map
`|a b c⟩ ↦ |a b (c ⊕ a·b)⟩`: its `(bitIdx a b c, bitIdx a' b' c')` entry is `1`
exactly when `a' = a`, `b' = b` and `c' = c + a * b` (arithmetic in `Fin 2`, i.e. XOR). -/
lemma toffoli_bitIdx (a b c a' b' c' : Fin 2) :
    toffoli (bitIdx a b c) (bitIdx a' b' c') =
      if a' = a ∧ b' = b ∧ c' = c + a * b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
    norm_num [toffoli, bitIdx, Fin.ext_iff]
  all_goals decide

/-- The Toffoli matrix is the permutation matrix of the transposition of the
basis indices `6 = |110⟩` and `7 = |111⟩`. -/
lemma toffoli_eq_permMatrix : toffoli = (Equiv.swap (6 : Fin 8) 7).permMatrix ℂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.swap_apply_def]

/-- The Toffoli matrix is real symmetric, so its conjugate transpose is itself. -/
lemma toffoli_conjTranspose : toffoliᴴ = toffoli := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toffoli, Matrix.conjTranspose_apply]

/-- The Toffoli matrix is its own inverse. -/
lemma toffoli_mul_self : toffoli * toffoli = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, Matrix.mul_apply, Fin.sum_univ_succ]

/-- **Toffoli is unitary.**  The Toffoli (CCNOT) matrix, a permutation matrix,
belongs to the unitary group, satisfies `Tᴴ * T = T * Tᴴ = 1`, and is its own
inverse (`T * T = 1`, `Tᴴ = T`). -/
theorem toffoli_unitary :
    toffoli ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧
      toffoliᴴ * toffoli = 1 ∧ toffoli * toffoliᴴ = 1 ∧
      toffoliᴴ = toffoli ∧ toffoli * toffoli = 1 := by
  have hH : toffoliᴴ = toffoli := toffoli_conjTranspose
  have hmul : toffoli * toffoli = 1 := toffoli_mul_self
  refine ⟨?_, ?_, ?_, hH, hmul⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    simpa [Matrix.star_eq_conjTranspose, hH] using hmul
  · rw [hH]; exact hmul
  · rw [hH]; exact hmul

end QC

