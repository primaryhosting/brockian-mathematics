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

lemma Pmat_mul_Qmat : Pmat * Qmat = 1 := by
  ext j l
  simp only [Matrix.mul_apply, Pmat, Qmat, Matrix.of_apply]
  have h : ∀ k : ZMod 9, psi (j * k) * (psi (-(k * l)) / 9) = psi (k * (j - l)) / 9 := by
    intro k
    rw [mul_div_assoc']
    congr 1
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.sum_div, psi_sum, Matrix.one_apply]
  rcases eq_or_ne j l with hjl | hjl
  · simp [hjl]
  · rw [if_neg (sub_ne_zero.mpr hjl), if_neg hjl]
    simp

