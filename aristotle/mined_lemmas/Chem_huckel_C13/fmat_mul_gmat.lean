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

set_option grind.warning false

namespace Chem

open Polynomial Complex

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The cycle graph `C₁₃`, on the vertex set `ZMod 13`, where `i` and `j` are adjacent
iff they differ by `1`. -/

lemma fmat_mul_gmat : fmat * gmat = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [fmat, gmat]
  have h : ∀ k : ZMod 13, ee (i * k) * ((13 : ℂ)⁻¹ * ee (-(k * j))) =
      (13 : ℂ)⁻¹ * ee (k * (i - j)) := by
    intro k
    rw [show k * (i - j) = i * k + -(k * j) by ring, ee_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, sum_ee_mul]
  by_cases hij : i = j
  · simp [hij, Matrix.one_apply]
  · have h0 : i - j ≠ 0 := sub_ne_zero.mpr hij
    simp [h0, hij]

