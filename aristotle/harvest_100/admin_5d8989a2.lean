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

import Mathlib
/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open NormedSpace

namespace QPhys

section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

noncomputable local instance instNormedAlgebraRatOfReal : NormedAlgebra ℚ 𝔸 :=
  NormedAlgebra.restrictScalars ℚ ℝ 𝔸

omit [CompleteSpace 𝔸] in
/-- A function `ℝ → 𝔸` with everywhere-vanishing derivative is constant. -/
theorem const_of_hasDerivAt_zero (F : ℝ → 𝔸) (h : ∀ t, HasDerivAt F 0 t) (t : ℝ) :
    F t = F 0 :=
  is_const_of_deriv_eq_zero (fun x => (h x).differentiableAt) (fun x => (h x).deriv) t 0

theorem exp_smul_mul_exp_neg_smul (x : 𝔸) (t : ℝ) : exp (t • x) * exp ((-t) • x) = 1 := by
  rw [← exp_add_of_commute ((Commute.refl x).smul_left t |>.smul_right (-t)), ← add_smul]
  simp

theorem hasDerivAt_exp_neg_smul (x : 𝔸) (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp ((-u) • x)) (-(exp ((-t) • x) * x)) t := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) x (-t)).scomp t (hasDerivAt_neg t)
  simp only [Function.comp_def, neg_one_smul] at h
  exact h

/-- Uniqueness for the linear ODE `Y' = M * Y` with zero initial condition. -/
theorem eq_zero_of_hasDerivAt_mul (M : 𝔸) (Y : ℝ → 𝔸) (h : ∀ t, HasDerivAt Y (M * Y t) t)
    (h0 : Y 0 = 0) (t : ℝ) : Y t = 0 := by
  set H : ℝ → 𝔸 := fun u => exp ((-u) • M) * Y u with hH
  have hHd : ∀ u : ℝ, HasDerivAt H 0 u := by
    intro u
    have := (hasDerivAt_exp_neg_smul M u).mul (h u)
    have hzero : -(exp ((-u) • M) * M) * Y u + exp ((-u) • M) * (M * Y u) = 0 := by
      rw [neg_mul, mul_assoc, neg_add_cancel]
    rw [hzero] at this
    exact this
  have hconst := const_of_hasDerivAt_zero H hHd t
  have hH0 : H 0 = 0 := by simp [hH, h0]
  have hHt : exp ((-t) • M) * Y t = 0 := by rw [← hH0, ← hconst]
  calc Y t = (exp (t • M) * exp ((-t) • M)) * Y t := by
        rw [exp_smul_mul_exp_neg_smul, one_mul]
    _ = exp (t • M) * (exp ((-t) • M) * Y t) := by rw [mul_assoc]
    _ = 0 := by rw [hHt, mul_zero]

/-- If `C = [A,B]` commutes with `A`, then `e^{tA} B = (B + tC) e^{tA}`. -/
theorem exp_smul_mul_eq (A B : 𝔸) (hA : Commute A (A * B - B * A)) (t : ℝ) :
    exp (t • A) * B = (B + t • (A * B - B * A)) * exp (t • A) := by
  set C : 𝔸 := A * B - B * A with hC
  have key : ∀ s : ℝ, A * (B + s • C) = C + (B + s • C) * A := by
    intro s
    have h1 : A * (s • C) = (s • C) * A := by
      rw [mul_smul_comm, smul_mul_assoc, hA]
    have h2 : A * B = C + B * A := by rw [hC]; abel
    rw [mul_add, h1, h2, add_mul]
    abel
  set Y : ℝ → 𝔸 := fun s => exp (s • A) * B - (B + s • C) * exp (s • A) with hY
  have hYd : ∀ s : ℝ, HasDerivAt Y (A * Y s) s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => exp (u • A) * B) ((A * exp (s • A)) * B) s :=
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s).mul_const B
    have hlin : HasDerivAt (fun u : ℝ => B + u • C) C s := by
      simpa using ((hasDerivAt_id s).smul_const C).const_add B
    have h2 : HasDerivAt (fun u : ℝ => (B + u • C) * exp (u • A))
        (C * exp (s • A) + (B + s • C) * (A * exp (s • A))) s :=
      hlin.mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s)
    have heq : A * Y s
        = (A * exp (s • A)) * B - (C * exp (s • A) + (B + s • C) * (A * exp (s • A))) := by
      show A * (exp (s • A) * B - (B + s • C) * exp (s • A)) = _
      rw [mul_sub, ← mul_assoc, ← mul_assoc, key s, add_mul,
        mul_assoc (B + s • C) A (exp (s • A))]
    rw [heq]
    exact h1.sub h2
  have h0 : Y 0 = 0 := by simp [hY]
  have := eq_zero_of_hasDerivAt_mul A Y hYd h0 t
  rw [hY] at this
  simp only [sub_eq_zero] at this
  exact this

/-- The path `t ↦ e^{tA} e^{tB}` solves the ODE `f' = (A + B + tC) f`. -/
theorem hasDerivAt_exp_mul_exp (A B C : 𝔸) (hC : A * B - B * A = C) (hAC : Commute A C) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • A) * exp (s • B))
      ((A + B + t • C) * (exp (t • A) * exp (t • B))) t := by
  have h1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t).mul
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) B t)
  have hkey : exp (t • A) * B = (B + t • C) * exp (t • A) := by
    rw [← hC] at hAC ⊢
    exact exp_smul_mul_eq A B hAC t
  have heq : (A + B + t • C) * (exp (t • A) * exp (t • B))
      = A * exp (t • A) * exp (t • B) + exp (t • A) * (B * exp (t • B)) := by
    rw [← mul_assoc (exp (t • A)) B, hkey, add_assoc, add_mul, mul_assoc A, mul_assoc (B + t • C)]
  rw [heq]
  exact h1

/-- The inverse path `t ↦ e^{-t(A+B)} e^{-t²C/2}` solves the ODE `h' = -h (A + B + tC)`. -/
theorem hasDerivAt_gi (A B C : 𝔸) (hAC : Commute A C) (hBC : Commute B C) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp ((-s) • (A + B)) * exp ((-(s ^ 2 / 2)) • C))
      (-((exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * (A + B + t • C))) t := by
  have hABC : Commute (A + B) C := hAC.add_left hBC
  have hp := hasDerivAt_exp_neg_smul (A + B) t
  have hinner : HasDerivAt (fun s : ℝ => -(s ^ 2 / 2)) (-t) t := by
    have : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
      simpa using ((hasDerivAt_pow 2 t).div_const 2)
    simpa using this.neg
  have hq : HasDerivAt (fun s : ℝ => exp ((-(s ^ 2 / 2)) • C))
      ((-t) • (exp ((-(t ^ 2 / 2)) • C) * C)) t := by
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) C (-(t ^ 2 / 2))).scomp t hinner
    simp only [Function.comp_def] at h
    exact h
  have hcomm : Commute (A + B) (exp ((-(t ^ 2 / 2)) • C)) :=
    (hABC.smul_right (-(t ^ 2 / 2))).exp_right
  have h := hp.mul hq
  have e1 : (exp ((-t) • (A + B)) * (A + B)) * exp ((-(t ^ 2 / 2)) • C)
      = (exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * (A + B) := by
    rw [mul_assoc, hcomm.eq, ← mul_assoc]
  have e2 : exp ((-t) • (A + B)) * ((-t) • (exp ((-(t ^ 2 / 2)) • C) * C))
      = (-t) • ((exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * C) := by
    rw [mul_smul_comm, mul_assoc]
  have heq : -(exp ((-t) • (A + B)) * (A + B)) * exp ((-(t ^ 2 / 2)) • C) +
      exp ((-t) • (A + B)) * ((-t) • (exp ((-(t ^ 2 / 2)) • C) * C))
      = -((exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * (A + B + t • C)) := by
    have e3 : (exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * (A + B + t • C)
        = (exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * (A + B)
          + t • ((exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * C) := by
      rw [mul_add (exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) (A + B) (t • C),
        mul_smul_comm]
    rw [neg_mul, e1, e2, e3, neg_add,
      neg_smul t (exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C) * C)]
  rw [← heq]
  exact h

/-- **Special case of the Baker–Campbell–Hausdorff formula.**
If the commutator `C = AB - BA` commutes with both `A` and `B` (in particular if it is central),
then `e^A e^B = e^{A + B + ½ [A,B]}`. -/
theorem bcH_special
    (A B : 𝔸) (hA : Commute A (A * B - B * A)) (hB : Commute B (A * B - B * A)) :
    exp A * exp B = exp (A + B + (1 / 2 : ℝ) • (A * B - B * A)) := by
  set C : 𝔸 := A * B - B * A with hC
  have hABC : Commute (A + B) C := hA.add_left hB
  set f : ℝ → 𝔸 := fun s => exp (s • A) * exp (s • B) with hf
  set gi : ℝ → 𝔸 := fun s => exp ((-s) • (A + B)) * exp ((-(s ^ 2 / 2)) • C) with hgi
  set D : ℝ → 𝔸 := fun s => gi s * f s with hD
  have hfd : ∀ s : ℝ, HasDerivAt f ((A + B + s • C) * f s) s := fun s =>
    hasDerivAt_exp_mul_exp A B C hC.symm hA s
  have hgid : ∀ s : ℝ, HasDerivAt gi (-(gi s * (A + B + s • C))) s := fun s =>
    hasDerivAt_gi A B C hA hB s
  have hDd : ∀ s : ℝ, HasDerivAt D 0 s := by
    intro s
    have h := (hgid s).mul (hfd s)
    have hz : -(gi s * (A + B + s • C)) * f s + gi s * ((A + B + s • C) * f s) = 0 := by
      rw [neg_mul, mul_assoc, neg_add_cancel]
    rw [hz] at h
    exact h
  have hD1 : D 1 = D 0 := const_of_hasDerivAt_zero D hDd 1
  have hD0 : D 0 = 1 := by simp [hD, hgi, hf]
  have hcomm : Commute (exp (((1 : ℝ) / 2) • C)) (exp (((-1 : ℝ)) • (A + B))) :=
    ((hABC.symm.smul_left ((1 : ℝ) / 2)).smul_right (-1 : ℝ)).exp
  have hone : (exp ((1 : ℝ) • (A + B)) * exp (((1 : ℝ) / 2) • C)) * gi 1 = 1 := by
    have h2 : ((1 : ℝ) ^ 2 / 2) = (1 : ℝ) / 2 := by norm_num
    simp only [hgi, h2]
    rw [mul_assoc, ← mul_assoc (exp (((1 : ℝ) / 2) • C)), hcomm.eq, mul_assoc,
      ← mul_assoc (exp ((1 : ℝ) • (A + B)))]
    rw [show ((-1 : ℝ)) = -(1 : ℝ) from rfl, exp_smul_mul_exp_neg_smul, one_mul]
    exact exp_smul_mul_exp_neg_smul C (1 / 2)
  have hfinal : f 1 = exp ((1 : ℝ) • (A + B)) * exp (((1 : ℝ) / 2) • C) := by
    calc f 1 = ((exp ((1 : ℝ) • (A + B)) * exp (((1 : ℝ) / 2) • C)) * gi 1) * f 1 := by
          rw [hone, one_mul]
      _ = (exp ((1 : ℝ) • (A + B)) * exp (((1 : ℝ) / 2) • C)) * D 1 := by
          rw [hD, mul_assoc]
      _ = exp ((1 : ℝ) • (A + B)) * exp (((1 : ℝ) / 2) • C) := by
          rw [hD1, hD0, mul_one]
  have hgoal : exp (A + B + ((1 : ℝ) / 2) • C)
      = exp ((1 : ℝ) • (A + B)) * exp (((1 : ℝ) / 2) • C) := by
    rw [one_smul, exp_add_of_commute (hABC.smul_right ((1 : ℝ) / 2))]
  rw [hgoal, ← hfinal, hf]
  simp

/-- **Baker–Campbell–Hausdorff, special case, with a central commutator.**
If `[A, B] = AB - BA` is central, then `e^A e^B = e^{A + B + ½ [A,B]}`. -/
theorem bcH_special_of_central (A B : 𝔸) (hcentral : ∀ x : 𝔸, Commute x (A * B - B * A)) :
    exp A * exp B = exp (A + B + (1 / 2 : ℝ) • (A * B - B * A)) :=
  bcH_special A B (hcentral A) (hcentral B)

end

end QPhys

