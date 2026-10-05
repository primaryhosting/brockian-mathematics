/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix SimpleGraph Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₀`.  This is the Hückel matrix of
cyclodecapentaene in units where the Coulomb integral `α` is `0` and the resonance integral
`β` is `1`. -/

noncomputable def dftU : Matrix (Fin 10) (Fin 10) ℂ :=
  Matrix.of fun j k : Fin 10 => zeta ^ (j.val * k.val)

set_option maxHeartbeats 4000000 in
example : (adjMatrix ℂ (cycleGraph 10)) * dftU
    = dftU * Matrix.diagonal (fun k : Fin 10 => zeta ^ (k : ℕ) + zeta ^ (10 - (k : ℕ))) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp +decide [dftU, Matrix.mul_apply, Fin.sum_univ_succ,
      SimpleGraph.adjMatrix_apply, Matrix.diagonal_apply, zeta_pow_sub_ten, cycle10_card] <;>
    ring_nf <;>
    simp only [zeta_pow_sub_ten, Nat.reduceSub, Nat.reduceLeDiff] <;>
    ring1

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

