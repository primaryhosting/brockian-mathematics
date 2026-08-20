import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
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

open Polynomial Matrix SimpleGraph

/-- A primitive 17-th root of unity. -/

lemma adjMatrix_mul_Fmat :
    ((cycleGraph 17).adjMatrix ℂ) * Fmat
      = Fmat * Matrix.diagonal (fun k => ((lam k : ℝ) : ℂ)) := by
  ext j k
  have hlhs : (((cycleGraph 17).adjMatrix ℂ) * Fmat) j k
      = ∑ u ∈ (cycleGraph 17).neighborFinset j, Fmat u k := by
    rw [Matrix.mul_apply]
    exact (SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (cycleGraph 17) j (fun m => Fmat m k))
  have hnb : (cycleGraph 17).neighborFinset j = {j - 1, j + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 15) (v := j)
  have hne : j - 1 ≠ j + 1 := Fin17_sub_one_ne_add_one j
  rw [hlhs, hnb, Finset.sum_pair hne, Matrix.mul_diagonal, lam_eq]
  -- compute the two shifted entries
  have hsub : ((j - 1 : Fin 17)).val = (j.val + 16) % 17 := by
    rw [Fin.sub_def]
    show (17 - (1 : Fin 17).val + j.val) % 17 = (j.val + 16) % 17
    norm_num
    omega
  have hadd : ((j + 1 : Fin 17)).val = (j.val + 1) % 17 := by
    rw [Fin.add_def]
    show (j.val + (1 : Fin 17).val) % 17 = (j.val + 1) % 17
    norm_num
  have e1 : Fmat (j - 1) k = zeta ^ (j.val * k.val + 16 * k.val) := by
    rw [Fmat_apply, hsub]
    refine zeta_pow_congr ?_
    have h := (Nat.mod_modEq (j.val + 16) 17).mul_right k.val
    calc (j.val + 16) % 17 * k.val ≡ (j.val + 16) * k.val [MOD 17] := h
      _ = j.val * k.val + 16 * k.val := by ring
  have e2 : Fmat (j + 1) k = zeta ^ (j.val * k.val + k.val) := by
    rw [Fmat_apply, hadd]
    refine zeta_pow_congr ?_
    have h := (Nat.mod_modEq (j.val + 1) 17).mul_right k.val
    calc (j.val + 1) % 17 * k.val ≡ (j.val + 1) * k.val [MOD 17] := h
      _ = j.val * k.val + k.val := by ring
  rw [e1, e2, Fmat_apply, pow_add, pow_add]
  ring

