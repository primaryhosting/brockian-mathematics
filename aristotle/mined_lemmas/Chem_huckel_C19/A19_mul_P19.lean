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

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma A19_mul_P19 :
    (SimpleGraph.cycleGraph 19).adjMatrix ℂ * P19 = P19 * D19 := by
  ext i k
  have hmul : ((SimpleGraph.cycleGraph 19).adjMatrix ℂ * P19) i k
      = ((SimpleGraph.cycleGraph 19).adjMatrix ℂ).mulVec (fun j => P19 j k) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hmul, SimpleGraph.adjMatrix_mulVec_apply,
    (SimpleGraph.cycleGraph_neighborFinset (n := 17) (v := i))]
  have hne : ∀ j : Fin 19, j - 1 ≠ j + 1 := by decide
  rw [Finset.sum_pair (hne i)]
  -- right-hand side
  rw [D19, Matrix.mul_diagonal]
  simp only [P19, Matrix.of_apply]
  -- exponent computations
  have hplus : ((i + 1 : Fin 19)).val * k.val ≡ i.val * k.val + k.val [MOD 19] := by
    have h1 : ((i + 1 : Fin 19)).val = (i.val + 1) % 19 := by
      rw [Fin.val_add]
      rfl
    calc ((i + 1 : Fin 19)).val * k.val = ((i.val + 1) % 19) * k.val := by rw [h1]
      _ ≡ (i.val + 1) * k.val [MOD 19] := Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
      _ = i.val * k.val + k.val := by ring
  have hminus : ((i - 1 : Fin 19)).val * k.val ≡ i.val * k.val + 18 * k.val [MOD 19] := by
    have h1 : ((i - 1 : Fin 19)).val = (18 + i.val) % 19 := by
      simp [Fin.sub_def]
    calc ((i - 1 : Fin 19)).val * k.val = ((18 + i.val) % 19) * k.val := by
          rw [h1]
      _ ≡ (18 + i.val) * k.val [MOD 19] := Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
      _ = i.val * k.val + 18 * k.val := by ring
  rw [zeta19_pow_congr hplus, zeta19_pow_congr hminus]
  have h18 : zeta19 ^ (18 * k.val) = (zeta19 ^ k.val)⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_add, show k.val + 18 * k.val = 19 * k.val by ring, pow_mul, zeta19_pow_19,
      one_pow]
  rw [pow_add, pow_add, h18, ← zeta19_pow_add_inv k.val]
  ring

