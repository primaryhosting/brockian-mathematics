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

lemma Gm_mul_C12adj : Gm * C12adj = Dm * Gm := by
  ext k l
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have h : ∀ j : ZMod 12, Gm k j * C12adj j l
      = (fun j : ZMod 12 => xi (-(k * j))) j * (if l = j + 1 ∨ l = j - 1 then (1 : ℂ) else 0) :=
    fun j => rfl
  rw [Finset.sum_congr rfl (fun j _ => h j), sum_indicator_right]
  have e1 : xi (-(k * (l - 1))) = xi (-(k * l)) * xi k := by
    rw [← xi_add]; congr 1; ring
  have e2 : xi (-(k * (l + 1))) = xi (-(k * l)) * xi (-k) := by
    rw [← xi_add]; congr 1; ring
  rw [e1, e2]
  have hD : ∀ j : ZMod 12, Dm k j * Gm j l = if j = k then lam k * xi (-(k * l)) else 0 := by
    intro j
    show (Matrix.diagonal lam) k j * xi (-(j * l)) = _
    rw [Matrix.diagonal_apply]
    split_ifs with h1 h2 h2
    · subst h2; ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring
  rw [Finset.sum_congr rfl (fun j _ => hD j), Finset.sum_ite_eq' Finset.univ k
    (fun _ => lam k * xi (-(k * l)))]
  simp only [Finset.mem_univ, if_true]
  rw [← lam_eq k]
  ring

/-- Each `2 cos(2πk/12)` is an eigenvalue, with the Fourier vector as eigenvector. -/
