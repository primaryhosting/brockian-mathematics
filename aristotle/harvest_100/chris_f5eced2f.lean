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

import Mathlib

open scoped BigOperators
open scoped Classical
open Matrix

set_option maxHeartbeats 4000000

namespace QC

/-- The classical action of the Toffoli (CCNOT) gate on the eight computational basis
states of three qubits, indexed by `Fin 8` via `i = 4*b₂ + 2*b₁ + b₀`.  It flips the
target bit `b₀` exactly when both control bits `b₂`, `b₁` are `1`, i.e. it exchanges
`|110⟩ = 6` and `|111⟩ = 7` and fixes everything else. -/
def toffoliPerm : Equiv.Perm (Fin 8) := Equiv.swap 6 7

/-- The Toffoli (CCNOT) matrix: the permutation matrix of `toffoliPerm`. -/
def toffoli : Matrix (Fin 8) (Fin 8) ℂ := fun i j => if i = toffoliPerm j then 1 else 0

lemma toffoli_apply (i j : Fin 8) :
    toffoli i j = if i = toffoliPerm j then 1 else 0 := rfl

/-- `toffoli` is the explicit `8 × 8` CCNOT matrix. -/
lemma toffoli_eq_explicit :
    toffoli =
      !![1,0,0,0,0,0,0,0;
         0,1,0,0,0,0,0,0;
         0,0,1,0,0,0,0,0;
         0,0,0,1,0,0,0,0;
         0,0,0,0,1,0,0,0;
         0,0,0,0,0,1,0,0;
         0,0,0,0,0,0,0,1;
         0,0,0,0,0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, toffoliPerm, Equiv.swap_apply_def]

/-- The Toffoli permutation is an involution. -/
lemma toffoliPerm_involutive : Function.Involutive toffoliPerm := by
  intro x
  simp [toffoliPerm, Equiv.swap_apply_self]

/-- The Toffoli matrix is symmetric with real entries, hence self-adjoint. -/
lemma toffoli_conjTranspose : toffoliᴴ = toffoli := by
  ext i j
  rw [Matrix.conjTranspose_apply, toffoli_apply, toffoli_apply]
  by_cases h : j = toffoliPerm i
  · have h2 : i = toffoliPerm j := by rw [h, toffoliPerm_involutive]
    rw [if_pos h, if_pos h2, star_one]
  · have h2 : ¬ i = toffoliPerm j := fun hh => h (by rw [hh, toffoliPerm_involutive])
    rw [if_neg h, if_neg h2, star_zero]

/-- The Toffoli matrix is its own inverse. -/
lemma toffoli_mul_self : toffoli * toffoli = 1 := by
  ext i j
  simp only [Matrix.mul_apply, toffoli_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (toffoliPerm j)]
  · by_cases h : i = j
    · subst h
      simp [toffoliPerm_involutive i]
    · have : ¬ i = toffoliPerm (toffoliPerm j) := by
        rwa [toffoliPerm_involutive j]
      simp [this, h]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Index of the computational basis state `|b₂ b₁ b₀⟩` of three qubits. -/
def bitIdx (b₂ b₁ b₀ : Bool) : Fin 8 :=
  ⟨4 * b₂.toNat + 2 * b₁.toNat + b₀.toNat, by cases b₂ <;> cases b₁ <;> cases b₀ <;> decide⟩

/-- `toffoliPerm` implements the CCNOT truth table: the target bit `b₀` is flipped
exactly when both controls are set. -/
lemma toffoliPerm_bitIdx (b₂ b₁ b₀ : Bool) :
    toffoliPerm (bitIdx b₂ b₁ b₀) = bitIdx b₂ b₁ (xor b₀ (b₂ && b₁)) := by
  cases b₂ <;> cases b₁ <;> cases b₀ <;> decide

/-- `toffoli` is the permutation matrix of `toffoliPerm` in Mathlib's sense. -/
lemma toffoli_eq_permMatrix : toffoli = toffoliPerm.permMatrix ℂ := by
  ext i j
  rw [toffoli_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  by_cases h : i = toffoliPerm j
  · have : j = toffoliPerm i := by rw [h, toffoliPerm_involutive]
    rw [if_pos h, if_pos this.symm]
  · have : ¬ (toffoliPerm i = j) := fun hh => h (by rw [← hh, toffoliPerm_involutive])
    rw [if_neg h, if_neg this]

/-- The Toffoli matrix permutes the computational basis states according to CCNOT. -/
lemma toffoli_mulVec_basis (b₂ b₁ b₀ : Bool) :
    toffoli.mulVec (Pi.single (bitIdx b₂ b₁ b₀) (1 : ℂ))
      = Pi.single (bitIdx b₂ b₁ (xor b₀ (b₂ && b₁))) (1 : ℂ) := by
  funext i
  rw [Matrix.mulVec_single_one]
  simp only [Matrix.col_apply, toffoli_apply, toffoliPerm_bitIdx]
  by_cases h : i = bitIdx b₂ b₁ (xor b₀ (b₂ && b₁))
  · rw [if_pos h, h, Pi.single_eq_same]
  · rw [if_neg h, Pi.single_eq_of_ne h]

/-- **The Toffoli (CCNOT) matrix is a permutation matrix, hence unitary, and it is its
own inverse.** -/
theorem toffoli_unitary :
    toffoli ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧
      toffoli * toffoliᴴ = 1 ∧ toffoliᴴ * toffoli = 1 ∧ toffoli * toffoli = 1 := by
  have h := toffoli_mul_self
  have hc := toffoli_conjTranspose
  refine ⟨?_, ?_, ?_, h⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hc]
    exact h
  · rw [hc]; exact h
  · rw [hc]; exact h

end QC

