import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option grind.warning false

namespace Chem

open Matrix SimpleGraph

/-- A primitive 19-th root of unity. -/

theorem adj_mul_dft19 :
    (SimpleGraph.cycleGraph 19).adjMatrix ℂ * dft19 = dft19 * Matrix.diagonal eig19 := by
  ext i k
  have hlhs : ((SimpleGraph.cycleGraph 19).adjMatrix ℂ * dft19) i k
      = ∑ u ∈ (SimpleGraph.cycleGraph 19).neighborFinset i, dft19 u k := by
    rw [Matrix.mul_apply]
    have h := SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (SimpleGraph.cycleGraph 19) i
      (fun j => dft19 j k)
    rw [← h]
    rfl
  rw [hlhs]
  have hnb : (SimpleGraph.cycleGraph 19).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 17) (v := i)
  rw [hnb]
  have hne : i - 1 ≠ i + 1 := by
    simp only [ne_eq, Fin.ext_iff, Fin.sub_def, Fin.add_def]
    omega
  rw [Finset.sum_pair hne, Matrix.mul_diagonal]
  have e1 : dft19 (i - 1) k = om ^ (18 * k.val) * om ^ (i.val * k.val) := by
    have hv : (i - 1 : Fin 19).val = (18 + i.val) % 19 := by
      rw [Fin.sub_def]; simp
    simp only [dft19, Matrix.of_apply, hv]
    rw [← pow_add]
    refine om_pow_congr ?_
    rw [show 18 * k.val + i.val * k.val = (18 + i.val) * k.val by ring]
    exact Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
  have e2 : dft19 (i + 1) k = om ^ (i.val * k.val) * om ^ k.val := by
    have hv : (i + 1 : Fin 19).val = (i.val + 1) % 19 := by
      rw [Fin.add_def]; simp
    simp only [dft19, Matrix.of_apply, hv]
    rw [← pow_add]
    refine om_pow_congr ?_
    rw [show i.val * k.val + k.val = (i.val + 1) * k.val by ring]
    exact Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
  have e0 : dft19 i k = om ^ (i.val * k.val) := rfl
  rw [e1, e2, e0, ← eig19_eq k]
  ring

/-- **Hückel theory for the cyclic polyene C₁₉.**
The spectrum of the adjacency matrix of the cycle graph `C₁₉` is exactly
`{2 cos (2πk/19) : k = 0, …, 18}`. -/
