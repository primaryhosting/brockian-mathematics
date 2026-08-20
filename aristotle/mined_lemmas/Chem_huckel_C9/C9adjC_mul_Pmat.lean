import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede all other commands, including module
docstrings, so the required header comment appears immediately after the import.)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₉`, with vertices indexed by `ZMod 9`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `9`. -/

lemma C9adjC_mul_Pmat : C9adjC * Pmat = Pmat * Dmat := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [Dmat]
  rw [Matrix.mul_diagonal]
  have hentry : ∀ j : ZMod 9, C9adjC i j * Pmat j k
      = (if j = i - 1 then psi (j * k) else 0) + (if j = i + 1 then psi (j * k) else 0) := by
    intro j
    simp only [C9adjC, Matrix.map_apply, Pmat, Matrix.of_apply, C9adj_entry i j]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => hentry j, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]
  simp only [Pmat, Matrix.of_apply]
  have h1 : psi ((i - 1) * k) = psi (i * k) * psi (-k) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have h2 : psi ((i + 1) * k) = psi (i * k) * psi k := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  rw [h1, h2, ← mul_add, add_comm (psi (-k)) (psi k), psi_add_psi_neg]

/-- The unit given by the DFT matrix. -/
