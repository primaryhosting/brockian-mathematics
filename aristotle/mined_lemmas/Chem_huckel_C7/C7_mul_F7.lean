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

open Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `±1` mod `7`. -/

private lemma C7_mul_F7 :
    (C7.map (algebraMap ℝ ℂ)) * F7 = F7 * Matrix.diagonal (fun k : ZMod 7 =>
      (algebraMap ℝ ℂ) (C7eigen k.val)) := by
  have hcond : ∀ i j : ZMod 7, ((i - j = 1 ∨ i - j = -1) ↔ (j = i - 1 ∨ j = i + 1)) := by decide
  have hne : ∀ i : ZMod 7, (i - 1 : ZMod 7) ≠ i + 1 := by decide
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hsum : ∀ j : ZMod 7, (C7.map (algebraMap ℝ ℂ)) i j * F7 j k
      = (if j = i - 1 then ZMod.stdAddChar (j * k) else 0)
        + (if j = i + 1 then ZMod.stdAddChar (j * k) else 0) := by
    intro j
    simp only [C7, F7, Matrix.map_apply, Matrix.of_apply, hcond i j]
    by_cases h1 : j = i - 1
    · have h2 : j ≠ i + 1 := by rw [h1]; exact hne i
      simp [h1, hne i]
    · by_cases h2 : j = i + 1 <;> simp [h1, h2, Ne.symm (hne i)]
  rw [Finset.sum_congr rfl (fun j _ => hsum j), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [F7, Matrix.of_apply, Complex.coe_algebraMap]
  have hk : ((k.val : ZMod 7)) = k := by simp [ZMod.natCast_val, ZMod.cast_id]
  have e1 : ((i - 1) * k : ZMod 7) = i * k + (-(k.val : ZMod 7)) := by rw [hk]; ring
  have e2 : ((i + 1) * k : ZMod 7) = i * k + ((k.val : ZMod 7)) := by rw [hk]; ring
  rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← mul_add, add_comm
    (ZMod.stdAddChar (-(k.val : ZMod 7))), char_add_neg]

