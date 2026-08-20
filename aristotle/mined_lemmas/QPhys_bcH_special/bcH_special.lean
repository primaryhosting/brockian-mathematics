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

namespace QPhys

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- In a Banach algebra, `exp (x + y) = exp x * exp y` for commuting `x`, `y`. -/

theorem bcH_special (A B : 𝔸) (hcentral : ∀ x : 𝔸, Commute (A * B - B * A) x) :
    exp A * exp B = exp (A + B + (1 / 2 : ℝ) • (A * B - B * A)) := by
  set C := A * B - B * A with hCdef
  have key : ∀ s : ℝ, HasDerivAt (fun u : ℝ =>
      exp (u • (-(A + B))) * exp ((u ^ 2 / 2) • (-C)) * (exp (u • A) * exp (u • B))) 0 s := by
    intro s
    have hW : HasDerivAt (fun u : ℝ => exp (u • (-(A + B)))) (exp (s • (-(A + B))) * (-(A + B))) s :=
      hasDerivAt_exp_smul_const _ s
    have hZ : HasDerivAt (fun u : ℝ => exp ((u ^ 2 / 2) • (-C)))
        (s • (exp ((s ^ 2 / 2) • (-C)) * (-C))) s := by
      have h₁ := hasDerivAt_exp_smul_const (-C) (s ^ 2 / 2)
      have h₂ : HasDerivAt (fun u : ℝ => u ^ 2 / 2) s s := by
        simpa using ((hasDerivAt_pow 2 s).div_const 2)
      simpa [Function.comp] using h₁.scomp s h₂
    have hU : HasDerivAt (fun u : ℝ => exp (u • A)) (exp (s • A) * A) s :=
      hasDerivAt_exp_smul_const A s
    have hV : HasDerivAt (fun u : ℝ => exp (u • B)) (exp (s • B) * B) s :=
      hasDerivAt_exp_smul_const B s
    have hk := (hW.mul hZ).mul (hU.mul hV)
    simp only [Pi.mul_apply] at hk
    have hZc : ∀ x : 𝔸, exp ((s ^ 2 / 2) • (-C)) * x = x * exp ((s ^ 2 / 2) • (-C)) :=
      fun x => ((((hcentral x).neg_left).smul_left (s ^ 2 / 2)).exp_left).eq
    have hUA : exp (s • A) * A = A * exp (s • A) := (((Commute.refl A).smul_left s).exp_left).eq
    have hVB : exp (s • B) * B = B * exp (s • B) := (((Commute.refl B).smul_left s).exp_left).eq
    have hUB : exp (s • A) * B = (B + s • C) * exp (s • A) :=
      exp_mul_of_central A B C hCdef.symm hcentral s
    have hzero : (exp (s • (-(A + B))) * (-(A + B)) * exp ((s ^ 2 / 2) • (-C))
          + exp (s • (-(A + B))) * (s • (exp ((s ^ 2 / 2) • (-C)) * (-C))))
            * (exp (s • A) * exp (s • B))
        + exp (s • (-(A + B))) * exp ((s ^ 2 / 2) • (-C))
            * (exp (s • A) * A * exp (s • B) + exp (s • A) * (exp (s • B) * B)) = 0 := by
      set W := exp (s • (-(A + B)))
      set Z := exp ((s ^ 2 / 2) • (-C))
      set U := exp (s • A)
      set V := exp (s • B)
      have k1 : W * -(A + B) * Z * (U * V) = -(W * Z * A * (U * V)) - W * Z * B * (U * V) := by
        rw [mul_assoc W, ← hZc (-(A + B))]; noncomm_ring
      have k2 : W * (s • (Z * -C)) * (U * V) = -(s • (W * Z * C * (U * V))) := by
        have h : W * (Z * -C) * (U * V) = -(W * Z * C * (U * V)) := by noncomm_ring
        rw [mul_smul_comm, smul_mul_assoc, h, smul_neg]
      have k3 : W * Z * (U * A * V) = W * Z * A * (U * V) := by rw [hUA]; noncomm_ring
      have k4 : W * Z * (U * (V * B)) = W * Z * B * (U * V) + s • (W * Z * C * (U * V)) := by
        rw [hVB, ← mul_assoc U, hUB, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, mul_add,
          mul_smul_comm]
        congr 1 <;> noncomm_ring
      rw [add_mul, mul_add, k1, k2, k3, k4]
      abel
    rw [hzero] at hk
    exact hk
  have hdiff : Differentiable ℝ (fun u : ℝ =>
      exp (u • (-(A + B))) * exp ((u ^ 2 / 2) • (-C)) * (exp (u • A) * exp (u • B))) :=
    fun s => (key s).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun s => (key s).deriv) 1 0
  simp only [one_smul, one_pow, zero_smul, show ((0 : ℝ) ^ 2 / 2) = 0 by norm_num,
    NormedSpace.exp_zero, mul_one] at hconst
  -- `hconst : exp (-(A+B)) * exp ((1/2 : ℝ) • (-C)) * (exp A * exp B) = 1`
  have hcomm : Commute (-(A + B)) (((1 : ℝ) / 2) • (-C)) :=
    (((hcentral (-(A + B))).neg_left).smul_left ((1 : ℝ) / 2)).symm
  have hsplit : exp (-(A + B)) * exp (((1 : ℝ) / 2) • (-C))
      = exp (-(A + B + ((1 : ℝ) / 2) • C)) := by
    rw [← exp_add_of_commute' hcomm]
    congr 1
    module
  rw [hsplit] at hconst
  calc exp A * exp B
      = exp (A + B + ((1 : ℝ) / 2) • C) * exp (-(A + B + ((1 : ℝ) / 2) • C)) * (exp A * exp B) := by
        rw [exp_mul_exp_neg, one_mul]
    _ = exp (A + B + ((1 : ℝ) / 2) • C) * (exp (-(A + B + ((1 : ℝ) / 2) • C)) * (exp A * exp B)) := by
        rw [mul_assoc]
    _ = exp (A + B + ((1 : ℝ) / 2) • C) := by rw [hconst, mul_one]

end QPhys

