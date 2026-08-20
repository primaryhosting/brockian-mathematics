/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module docstring before the import commands, so the required
header appears here as an ordinary block comment; the text is otherwise verbatim.)
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

namespace Chem

open Complex Polynomial Matrix SimpleGraph

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₆`, i.e. the Hückel matrix of
cyclic C₁₆ in units where the Coulomb integral is `0` and the resonance integral is `1`. -/

theorem C16Adj_mul_Umat : C16Adj * Umat = Umat * Dmat := by
  ext i j
  have hne : i - 1 ≠ i + 1 := by revert i; decide
  have key : ∀ k : Fin 16, C16Adj i k * Umat k j
      = (if k = i - 1 then Umat k j else 0) + (if k = i + 1 then Umat k j else 0) := by
    intro k
    rw [C16Adj, SimpleGraph.adjMatrix_apply, if_congr (c16_adj_iff i k) rfl rfl]
    by_cases h1 : k = i - 1 <;> by_cases h2 : k = i + 1 <;> simp_all
  rw [Matrix.mul_apply]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ, Finset.mem_univ,
    if_pos]
  have e1 : Umat (i - 1) j = echar (i * j) * (echar j)⁻¹ := by
    simp only [Umat, Matrix.of_apply]
    rw [show (i - 1) * j = i * j + (-j) by rw [sub_mul, one_mul, sub_eq_add_neg], echar_add,
      echar_neg]
  have e2 : Umat (i + 1) j = echar (i * j) * echar j := by
    simp only [Umat, Matrix.of_apply]
    rw [show (i + 1) * j = i * j + j by rw [add_mul, one_mul], echar_add]
  rw [e1, e2, Dmat, Matrix.mul_diagonal, ← mul_add, add_comm ((echar j)⁻¹), echar_add_inv]
  simp [Umat]

