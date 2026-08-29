/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ### The shift matrices

`U n` is the matrix of the `n`-fold cyclic shift on `Fin 16`; the adjacency matrix of the
cycle graph `C₁₆` is `U 1 + U 15`. -/

/-- The matrix of the `n`-fold cyclic shift of `Fin 16`. -/

theorem spectrum_subset :
    spectrum ℂ ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) ⊆
      {z : ℂ | ∃ k : Fin 16, z = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 16)} := by
  intro w hw
  have hmem : Polynomial.eval w huckelPoly ∈
      spectrum ℂ (aeval ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) huckelPoly) :=
    spectrum.subset_polynomial_aeval _ huckelPoly ⟨w, hw, rfl⟩
  rw [aeval_huckelPoly, spectrum.zero_eq] at hmem
  have hzero : Polynomial.eval w huckelPoly = 0 := hmem
  rw [huckelPoly, Polynomial.eval_prod] at hzero
  simp only [eval_sub, eval_X, eval_C] at hzero
  obtain ⟨k, hk, hk0⟩ := Finset.prod_eq_zero_iff.1 hzero
  simp only [Finset.mem_range] at hk
  refine ⟨⟨k, hk⟩, ?_⟩
  have : w = lamC k := sub_eq_zero.1 hk0
  rw [this, lamC]

