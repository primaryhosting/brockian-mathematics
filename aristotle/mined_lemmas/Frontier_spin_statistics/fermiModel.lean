/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open scoped InnerProductSpace

namespace Frontier

/-! ## Minkowski geometry -/

/-- The Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`. -/

noncomputable def fermiModel : WightmanField Hf (Fin 4 → ℝ) where
  supp x := {x}
  field x := op (fieldMat x)
  fieldAdj x := op ((fieldMat x)ᴴ)
  adj_spec x u v := op_adj (fieldMat x) u v
  vacuum := vac
  twiceSpin := 1
  stat := Statistics.fermi
  locality x y h := by
    have ha := fieldMat_anticomm (h x rfl y rfl)
    have key : fieldMat x * (fieldMat y)ᴴ = -((fieldMat y)ᴴ * fieldMat x) :=
      eq_neg_of_add_eq_zero_left ha
    rw [op_comp, op_comp, Statistics.sign, neg_one_smul, key, op_neg]
  jost x y h := by
    have ho := coeff_orthogonal (h x rfl y rfl)
    have h1 : (op (fieldMat x)) ((op ((fieldMat y)ᴴ)) vac)
        = (op (fieldMat x * (fieldMat y)ᴴ)) vac := by
      rw [← op_comp]; rfl
    have h2 : (op ((fieldMat y)ᴴ)) ((op (fieldMat x)) vac)
        = (op ((fieldMat y)ᴴ * fieldMat x)) vac := by
      rw [← op_comp]; rfl
    rw [h1, h2, vev_op, vev_op, fieldMat_mul_adj, adj_mul_fieldMat]
    norm_num
    linear_combination ho
  analytic h := by
    exfalso
    have hx : cCoeff (fun _ => (0 : ℝ)) = 1 := by norm_num [cCoeff]
    have hy : cCoeff (fun i => if i = 1 then (1 : ℝ) else 0) = 1 := by
      norm_num [cCoeff, show (3 : Fin 4) ≠ 1 by decide, show (2 : Fin 4) ≠ 1 by decide]
    have hval := h (fun _ => (0 : ℝ)) (fun i => if i = 1 then 1 else 0)
      (by rintro u rfl v rfl; exact spacelike_example)
    have h2 : (op ((fieldMat (fun i => if i = 1 then (1 : ℝ) else 0))ᴴ))
        ((op (fieldMat (fun _ => (0 : ℝ)))) vac)
        = (op ((fieldMat (fun i => if i = 1 then (1 : ℝ) else 0))ᴴ
            * fieldMat (fun _ => (0 : ℝ)))) vac := by
      rw [← op_comp]; rfl
    rw [h2, vev_op, adj_mul_fieldMat] at hval
    norm_num [hx, hy] at hval
  separating x h := by
    have hc : cCoeff x = 0 := by
      have hentry := op_entry (fieldMat x) 1 0
      rw [show (EuclideanSpace.single 0 (1 : ℂ) : Hf) = vac from rfl, h] at hentry
      simp only [inner_zero_right] at hentry
      simpa [fieldMat] using hentry.symm
    have hd : dCoeff x = 0 := dCoeff_eq_zero_of_cCoeff_eq_zero hc
    have hM : fieldMat x = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [fieldMat, hc, hd]
    rw [show op (fieldMat x) = op 0 by rw [hM], op, map_zero]

