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
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Chem

/-- Adjacency matrix of the cycle graph `C₆` (the Hückel connectivity matrix of benzene):
vertex `i` is adjacent to `i ± 1 mod 6`. -/

lemma eigenvalue_poly {μ : ℂ} {v : Fin 6 → ℂ} (hv : v ≠ 0) (h : C6adj.mulVec v = μ • v) :
    (μ - 2) * (μ - 1) * (μ + 1) * (μ + 2) = 0 := by
  have h2 : C6sq.mulVec v = (μ ^ 2) • v := by
    rw [← C6adj_mul_self, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, h, smul_smul, sq]
  have h4 : (C6sq * C6sq).mulVec v = (μ ^ 4) • v := by
    rw [← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h2, smul_smul]
    ring_nf
  have hr : (C6sq * C6sq).mulVec v = (5 * μ ^ 2 - 4) • v := by
    rw [C6sq_mul_self, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, h2, smul_smul, sub_smul]
  have hz : (μ ^ 4 - (5 * μ ^ 2 - 4)) • v = 0 := by
    rw [sub_smul, ← h4, hr, sub_self]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have hzi := congrFun hz i
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_eq_zero] at hzi
  rcases hzi with hc | hc
  · linear_combination hc
  · exact absurd hc (by simpa using hi)

