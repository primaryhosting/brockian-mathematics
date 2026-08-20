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
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# The special case of the Baker–Campbell–Hausdorff formula

If the commutator `C = [A, B] = A * B - B * A` is central (it suffices that it commutes with
both `A` and `B`), then in a Banach algebra

`exp A * exp B = exp (A + B + ½ • [A, B])`.

The commuting case `[A,B] = 0` is `NormedSpace.exp_add_of_commute`; searches did not turn up
the statement below in Mathlib, so we prove it by the standard ODE argument: the curve
`t ↦ exp (tA) exp (tB) exp (-t²/2 • C) exp (-t • (A+B))` has vanishing derivative, hence is
constantly `1`.
-/

open NormedSpace

namespace QPhys

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `NormedSpace.exp_add_of_commute` for a real Banach algebra. -/
theorem exp_add_of_commute' {x y : 𝔸} (h : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_neg_mul_exp_self' (x : 𝔸) : exp (-x) * exp x = 1 := by
  rw [← exp_add_of_commute' ((Commute.refl x).neg_left), neg_add_cancel, exp_zero]

theorem exp_self_mul_exp_neg' (x : 𝔸) : exp x * exp (-x) = 1 := by
  rw [← exp_add_of_commute' ((Commute.refl x).neg_right), add_neg_cancel, exp_zero]

/-- Conjugation formula: if `[A,B]` commutes with `B`, then `e^{-tB} A e^{tB} = A + t[A,B]`. -/
theorem exp_conj_smul (A B : 𝔸) (hB : Commute B (A * B - B * A)) (t : ℝ) :
    exp (t • (-B)) * A * exp (t • B) = A + t • (A * B - B * A) := by
  set C := A * B - B * A with hC
  have hdF : ∀ s : ℝ, HasDerivAt (fun u : ℝ => exp (u • (-B)) * A * exp (u • B) - u • C) 0 s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => exp (u • (-B))) ((-B) * exp (s • (-B))) s :=
      hasDerivAt_exp_smul_const' (-B) s
    have h2 : HasDerivAt (fun u : ℝ => exp (u • B)) (exp (s • B) * B) s :=
      hasDerivAt_exp_smul_const B s
    have h3 := ((h1.mul_const A).mul h2).sub ((hasDerivAt_id s).smul_const C)
    convert h3 using 1
    have hcomm1 : Commute (exp (s • (-B))) B :=
      ((((Commute.refl B).neg_right).smul_right s).symm).exp_left
    have hcomm2 : Commute (exp (s • B)) C := (hB.smul_left s).exp_left
    have h2b : exp (s • B) * B = B * exp (s • B) :=
      (((Commute.refl B).smul_left s).exp_left).eq
    have hEE : exp (s • (-B)) * exp (s • B) = 1 := by
      rw [smul_neg, exp_neg_mul_exp_self']
    have hmain : (-B) * exp (s • (-B)) * A * exp (s • B) + exp (s • (-B)) * A * (exp (s • B) * B)
        = exp (s • (-B)) * C * exp (s • B) := by
      rw [← (hcomm1.neg_right).eq, h2b, hC]
      noncomm_ring
    rw [hmain, one_smul, mul_assoc, ← hcomm2.eq, ← mul_assoc, hEE, one_mul, sub_self]
  have h0 := is_const_of_deriv_eq_zero (fun s => (hdF s).differentiableAt)
      (fun s => (hdF s).deriv) t 0
  simp only [zero_smul, sub_zero, exp_zero, one_mul, mul_one] at h0
  rw [sub_eq_iff_eq_add] at h0
  exact h0

/-- Moving `A` past `e^{tB}` when `[A,B]` commutes with `B`. -/
theorem mul_exp_smul (A B : 𝔸) (hB : Commute B (A * B - B * A)) (t : ℝ) :
    A * exp (t • B) = exp (t • B) * (A + t • (A * B - B * A)) := by
  have h := congrArg (fun x => exp (t • B) * x) (exp_conj_smul A B hB t)
  simp only at h
  rw [← h, smul_neg, ← mul_assoc, ← mul_assoc, exp_self_mul_exp_neg', one_mul]

omit [CompleteSpace 𝔸] in
/-- The pointwise algebraic identity behind the vanishing of the derivative. -/
theorem bcH_deriv_cancel (A B C P Q R S : 𝔸) (s : ℝ)
    (e1 : A * Q = Q * (A + s • C)) (cRC : C * R = R * C)
    (hRA : R * (A * S) = A * (R * S)) (hRB : R * (B * S) = B * (R * S))
    (cS : (A + B) * S = S * (A + B)) :
    0 = ((P * A * Q + P * (Q * B)) * R + P * Q * (s • (R * (-C)))) * S
        + P * Q * R * (S * (-(A + B))) := by
  rw [mul_assoc P A Q, e1, mul_neg S (A + B), ← cS]
  simp only [mul_add, add_mul, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_assoc,
    ← cRC, hRA, hRB, smul_neg]
  abel

/-- The rescaled identity: `e^{tA} e^{tB} e^{-t²C/2} e^{-t(A+B)} = 1` for all real `t`. -/
theorem bcH_aux (A B : 𝔸) (hA : Commute A (A * B - B * A)) (hB : Commute B (A * B - B * A))
    (t : ℝ) :
    exp (t • A) * exp (t • B) * exp ((t ^ 2 / 2) • (-(A * B - B * A))) * exp (t • (-(A + B)))
      = 1 := by
  set C := A * B - B * A with hC
  have hd : ∀ s : ℝ, HasDerivAt
      (fun u : ℝ => exp (u • A) * exp (u • B) * exp ((u ^ 2 / 2) • (-C)) * exp (u • (-(A + B))))
      0 s := by
    intro s
    have hP : HasDerivAt (fun u : ℝ => exp (u • A)) (exp (s • A) * A) s :=
      hasDerivAt_exp_smul_const A s
    have hQ : HasDerivAt (fun u : ℝ => exp (u • B)) (exp (s • B) * B) s :=
      hasDerivAt_exp_smul_const B s
    have hS : HasDerivAt (fun u : ℝ => exp (u • (-(A + B)))) (exp (s • (-(A + B))) * (-(A + B))) s :=
      hasDerivAt_exp_smul_const _ s
    have hu : HasDerivAt (fun u : ℝ => u ^ 2 / 2) s s := by
      simpa using ((hasDerivAt_pow 2 s).div_const 2)
    have hR : HasDerivAt (fun u : ℝ => exp ((u ^ 2 / 2) • (-C)))
        (s • (exp ((s ^ 2 / 2) • (-C)) * (-C))) s := by
      have := (hasDerivAt_exp_smul_const (-C) (s ^ 2 / 2)).scomp s hu
      simpa [Function.comp] using this
    have h := (((hP.mul hQ).mul hR).mul hS)
    convert h using 1
    simp only [Pi.mul_apply]
    have cRA : Commute (exp ((s ^ 2 / 2) • (-C))) A :=
      ((hA.neg_right.smul_right (s ^ 2 / 2)).symm).exp_left
    have cRB : Commute (exp ((s ^ 2 / 2) • (-C))) B :=
      ((hB.neg_right.smul_right (s ^ 2 / 2)).symm).exp_left
    refine bcH_deriv_cancel A B C _ _ _ _ s (mul_exp_smul A B hB s) ?_ ?_ ?_ ?_
    · exact ((((Commute.refl C).neg_right).smul_right (s ^ 2 / 2)).exp_right).eq
    · rw [← mul_assoc, cRA.eq, mul_assoc]
    · rw [← mul_assoc, cRB.eq, mul_assoc]
    · exact (((Commute.refl (A + B)).neg_right).smul_right s).exp_right.eq
  have h0 := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa using h0

/-- **Special case of the Baker–Campbell–Hausdorff formula.**  In a real Banach algebra, if the
commutator `[A, B] = A * B - B * A` commutes with both `A` and `B` (in particular if it is
central), then `e^A e^B = e^{A + B + ½ [A,B]}`. -/
theorem bcH_special (A B : 𝔸) (hA : Commute A (A * B - B * A)) (hB : Commute B (A * B - B * A)) :
    exp A * exp B = exp (A + B + (2 : ℝ)⁻¹ • (A * B - B * A)) := by
  set C := A * B - B * A with hC
  have hcomm : Commute (A + B) ((2 : ℝ)⁻¹ • C) := (hA.add_left hB).smul_right _
  have h1 := bcH_aux A B hA hB 1
  simp only [one_smul, one_pow] at h1
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, smul_neg] at h1
  have h2 : exp A * exp B * exp (-((2 : ℝ)⁻¹ • C)) = exp (A + B) := by
    have h := congrArg (fun x => x * exp (A + B)) h1
    simp only [one_mul] at h
    rwa [mul_assoc _ (exp (-(A + B))) (exp (A + B)), exp_neg_mul_exp_self', mul_one] at h
  have h3 : exp A * exp B = exp (A + B) * exp ((2 : ℝ)⁻¹ • C) := by
    have h := congrArg (fun x => x * exp ((2 : ℝ)⁻¹ • C)) h2
    simp only at h
    rwa [mul_assoc _ (exp (-((2 : ℝ)⁻¹ • C))) (exp ((2 : ℝ)⁻¹ • C)), exp_neg_mul_exp_self',
      mul_one] at h
  rw [h3, exp_add_of_commute' hcomm]

end QPhys

