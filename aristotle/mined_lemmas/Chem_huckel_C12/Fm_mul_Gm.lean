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
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma Fm_mul_Gm : Fm * Gm = (12 : ℂ) • (1 : Matrix (ZMod 12) (ZMod 12) ℂ) := by
  ext k l
  rw [Matrix.mul_apply]
  have h : ∀ j : ZMod 12, Fm k j * Gm j l = xi (j * (k - l)) := by
    intro j
    show xi (k * j) * xi (-(j * l)) = xi (j * (k - l))
    rw [← xi_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun j _ => h j), sum_xi]
  by_cases hkl : k = l
  · subst hkl; simp
  · rw [if_neg (fun h => hkl (by linear_combination h))]
    simp [hkl]

/-- `Gm` intertwines the adjacency matrix with the diagonal matrix of eigenvalues. -/
