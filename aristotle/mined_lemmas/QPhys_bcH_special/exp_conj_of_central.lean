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

theorem exp_conj_of_central (A B C : 𝔸) (hC : A * B - B * A = C)
    (hcentral : ∀ x : 𝔸, Commute C x) (t : ℝ) :
    exp (t • A) * B * exp (-(t • A)) = B + t • C := by
  have key : ∀ s : ℝ, HasDerivAt (fun u : ℝ => exp (u • A) * B * exp (-(u • A)) - u • C) 0 s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => exp (u • A)) (exp (s • A) * A) s :=
      hasDerivAt_exp_smul_const A s
    have h2 : HasDerivAt (fun u : ℝ => exp (-(u • A))) (exp (-(s • A)) * (-A)) s := by
      have := hasDerivAt_exp_smul_const (-A) s
      simpa [smul_neg] using this
    have h5 := ((h1.mul_const B).mul h2).sub
      (by simpa using (hasDerivAt_id s).smul_const C :
        HasDerivAt (fun u : ℝ => u • C) C s)
    have hcomm : Commute A (exp (-(s • A))) :=
      (((Commute.refl A).smul_right s).neg_right).exp_right
    have e1 : exp (-(s • A)) * (-A) = (-A) * exp (-(s • A)) := by
      have h := hcomm.symm
      simp only [Commute, SemiconjBy] at h
      simp [mul_neg, neg_mul, h]
    have hXY : exp (s • A) * exp (-(s • A)) = 1 := exp_mul_exp_neg _
    have hzero : exp (s • A) * A * B * exp (-(s • A))
        + exp (s • A) * B * (exp (-(s • A)) * -A) - C = 0 := by
      rw [e1]
      have h6 : exp (s • A) * A * B * exp (-(s • A)) + exp (s • A) * B * (-A * exp (-(s • A)))
           = exp (s • A) * (C * exp (-(s • A))) := by
        rw [← hC]; noncomm_ring
      rw [h6, (hcentral (exp (-(s • A)))).eq, ← mul_assoc, hXY, one_mul, sub_self]
    rw [hzero] at h5
    exact h5
  have hdiff : Differentiable ℝ (fun u : ℝ => exp (u • A) * B * exp (-(u • A)) - u • C) :=
    fun s => (key s).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun s => (key s).deriv) t 0
  simp only [zero_smul, sub_zero, NormedSpace.exp_zero, one_mul, mul_one,
    neg_zero] at hconst
  have := hconst
  rw [sub_eq_iff_eq_add] at this
  simpa [add_comm] using this

/-- Commutation rule: `e^{tA} B = (B + t C) e^{tA}` when `C = [A,B]` is central. -/
