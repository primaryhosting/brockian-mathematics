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
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- written as an ordinary block comment.)

import Mathlib

/-!
## The special case of the Baker–Campbell–Hausdorff formula

If the commutator `C = A * B - B * A` commutes with both `A` and `B` (in particular if it is
central), then in a Banach algebra
`exp A * exp B = exp (A + B + ½ • (A * B - B * A))`.

Mathlib provides `NormedSpace.exp_add_of_commute` (the case `C = 0`) and the derivative
`hasDerivAt_exp_smul_const`, but not this refinement, so it is proved here by the classical
ODE argument: the function
`t ↦ exp (-(t²/2) • C) * exp (-t • (A+B)) * exp (t • A) * exp (t • B)`
has vanishing derivative, hence is constantly `1`.
-/

open NormedSpace

namespace QPhys

section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

omit [NormedAlgebra ℝ 𝔸] in
/-- Purely algebraic identity used for the derivative of the conjugation `s ↦ e^{-sA} (B + sC) e^{sA}`. -/
theorem conj_deriv_algebraic (u w m A C : 𝔸) (e1 : A * u = u * A) (e2 : A * w = w * A)
    (e3 : A * m = m * A + C) :
    (-(A * u) * m + u * C) * w + u * m * (w * A) = 0 := by
  calc (-(A * u) * m + u * C) * w + u * m * (w * A)
      = u * ((-(A * m) + C) + m * A) * w := by rw [e1, ← e2]; noncomm_ring
    _ = u * ((-(m * A + C) + C) + m * A) * w := by rw [e3]
    _ = 0 := by noncomm_ring

/-- Purely algebraic identity used for the derivative of
`t ↦ e^{-(t²/2)C} e^{-t(A+B)} e^{tA} e^{tB}`. -/
theorem bch_deriv_algebraic (u v w z A B C : 𝔸) (t : ℝ)
    (hCv : C * v = v * C) (hSv : (A + B) * v = v * (A + B))
    (hwB : w * B = B * w + t • (C * w)) (hzB : z * B = B * z) :
    ((((-t) • (u * C)) * v + u * (-((A + B) * v))) * w + (u * v) * (A * w)) * z
      + ((u * v) * w) * (z * B) = 0 := by
  have e1 : ((-t) • (u * C)) * v * w * z = (-t) • (u * v * (C * (w * z))) := by
    simp only [smul_mul_assoc]
    congr 1
    rw [mul_assoc u C v, hCv]
    noncomm_ring
  have e2 : u * (-((A + B) * v)) * w * z = -(u * v * (A * (w * z))) - u * v * (B * (w * z)) := by
    rw [hSv]; noncomm_ring
  have e3 : (u * v) * (A * w) * z = u * v * (A * (w * z)) := by noncomm_ring
  have e4 : ((u * v) * w) * (z * B) = u * v * (B * (w * z)) + t • (u * v * (C * (w * z))) := by
    rw [hzB]
    have h : (u * v * w) * (B * z) = (u * v) * ((w * B) * z) := by noncomm_ring
    rw [h, hwB, add_mul, smul_mul_assoc, mul_add, mul_smul_comm]
    congr 1 <;> noncomm_ring
  calc ((((-t) • (u * C)) * v + u * (-((A + B) * v))) * w + (u * v) * (A * w)) * z
        + ((u * v) * w) * (z * B)
      = ((-t) • (u * C)) * v * w * z + u * (-((A + B) * v)) * w * z + (u * v) * (A * w) * z
        + ((u * v) * w) * (z * B) := by noncomm_ring
    _ = 0 := by rw [e1, e2, e3, e4]; module

end

section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

noncomputable local instance ratAlg : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸

/-- `exp (r • X) * exp (-r • X) = 1`. -/
theorem exp_smul_mul_exp_neg_smul (X : 𝔸) (r : ℝ) : exp (r • X) * exp ((-r) • X) = 1 := by
  rw [← exp_add_of_commute (((Commute.refl X).smul_left r).smul_right (-r))]
  simp

/-- The derivative of `s ↦ exp (-s • X)`. -/
theorem hasDerivAt_exp_neg_smul (X : 𝔸) (s : ℝ) :
    HasDerivAt (fun r : ℝ => exp ((-r) • X)) (-(X * exp ((-s) • X))) s := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (-s)).scomp s (hasDerivAt_neg s)
  simpa [Function.comp_def] using h

/-- If `C = A * B - B * A` commutes with `A`, then `e^{tA} B = (B + t C) e^{tA}`. -/
theorem exp_smul_mul_eq (A B : 𝔸) (hA : Commute (A * B - B * A) A) (t : ℝ) :
    exp (t • A) * B = (B + t • (A * B - B * A)) * exp (t • A) := by
  set C := A * B - B * A with hC
  have hAC : A * C = C * A := hA.symm.eq
  have hAB : A * B = B * A + C := by rw [hC]; abel
  have hAm : ∀ s : ℝ, A * (B + s • C) = (B + s • C) * A + C := by
    intro s
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hAC, hAB]
    abel
  set f : ℝ → 𝔸 := fun s => exp ((-s) • A) * (B + s • C) * exp (s • A) with hf
  have key : ∀ s : ℝ, HasDerivAt f 0 s := by
    intro s
    have h1 : HasDerivAt (fun r : ℝ => exp ((-r) • A)) (-(A * exp ((-s) • A))) s :=
      hasDerivAt_exp_neg_smul A s
    have h2 : HasDerivAt (fun r : ℝ => B + r • C) C s := by
      simpa using ((hasDerivAt_id s).smul_const C).const_add B
    have h3 : HasDerivAt (fun r : ℝ => exp (r • A)) (exp (s • A) * A) s :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) A s
    have h : HasDerivAt f
        ((-(A * exp ((-s) • A)) * (B + s • C) + exp ((-s) • A) * C) * exp (s • A)
          + exp ((-s) • A) * (B + s • C) * (exp (s • A) * A)) s := (h1.mul h2).mul h3
    refine h.congr_deriv ?_
    exact conj_deriv_algebraic (exp ((-s) • A)) (exp (s • A)) (B + s • C) A C
      (((Commute.refl A).smul_right (-s)).exp_right.eq)
      (((Commute.refl A).smul_right s).exp_right.eq) (hAm s)
  have hconst : f t = f 0 :=
    is_const_of_deriv_eq_zero (fun x => (key x).differentiableAt) (fun x => (key x).deriv) t 0
  have h0 : f 0 = B := by simp [hf]
  have ht : exp ((-t) • A) * (B + t • C) * exp (t • A) = B := hconst.trans h0
  calc exp (t • A) * B = exp (t • A) * (exp ((-t) • A) * (B + t • C) * exp (t • A)) := by rw [ht]
    _ = (exp (t • A) * exp ((-t) • A)) * ((B + t • C) * exp (t • A)) := by noncomm_ring
    _ = (B + t • C) * exp (t • A) := by rw [exp_smul_mul_exp_neg_smul A t, one_mul]

/-- The one-parameter form of the special BCH formula:
`e^{tA} e^{tB} = e^{t(A+B)} e^{(t²/2) [A,B]}` when `[A,B]` commutes with `A` and `B`. -/
theorem exp_smul_mul_exp_smul (A B : 𝔸) (hA : Commute (A * B - B * A) A)
    (hB : Commute (A * B - B * A) B) (t : ℝ) :
    exp (t • A) * exp (t • B) = exp (t • (A + B)) * exp ((t ^ 2 / 2) • (A * B - B * A)) := by
  set C := A * B - B * A with hC
  have hCS : Commute C (A + B) := hA.add_right hB
  set H : ℝ → 𝔸 :=
    fun s => exp ((-(s ^ 2 / 2)) • C) * exp ((-s) • (A + B)) * exp (s • A) * exp (s • B) with hH
  have key : ∀ s : ℝ, HasDerivAt H 0 s := by
    intro s
    have h1 : HasDerivAt (fun r : ℝ => exp ((-(r ^ 2 / 2)) • C))
        ((-s) • (exp ((-(s ^ 2 / 2)) • C) * C)) s := by
      have hg : HasDerivAt (fun r : ℝ => -(r ^ 2 / 2)) (-s) s := by
        have h : HasDerivAt (fun r : ℝ => r ^ 2 / 2) s s := by
          simpa using ((hasDerivAt_pow 2 s).div_const 2)
        simpa using h.neg
      have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) C (-(s ^ 2 / 2))).scomp s hg
      simpa [Function.comp_def] using h
    have h2 : HasDerivAt (fun r : ℝ => exp ((-r) • (A + B)))
        (-((A + B) * exp ((-s) • (A + B)))) s := hasDerivAt_exp_neg_smul (A + B) s
    have h3 : HasDerivAt (fun r : ℝ => exp (r • A)) (A * exp (s • A)) s :=
      hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s
    have h4 : HasDerivAt (fun r : ℝ => exp (r • B)) (exp (s • B) * B) s :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) B s
    have h : HasDerivAt H
        (((((-s) • (exp ((-(s ^ 2 / 2)) • C) * C)) * exp ((-s) • (A + B))
            + exp ((-(s ^ 2 / 2)) • C) * (-((A + B) * exp ((-s) • (A + B))))) * exp (s • A)
          + (exp ((-(s ^ 2 / 2)) • C) * exp ((-s) • (A + B))) * (A * exp (s • A))) * exp (s • B)
          + ((exp ((-(s ^ 2 / 2)) • C) * exp ((-s) • (A + B))) * exp (s • A))
              * (exp (s • B) * B)) s := ((h1.mul h2).mul h3).mul h4
    refine h.congr_deriv ?_
    have hCv : C * exp ((-s) • (A + B)) = exp ((-s) • (A + B)) * C :=
      (hCS.smul_right (-s)).exp_right.eq
    have hSv : (A + B) * exp ((-s) • (A + B)) = exp ((-s) • (A + B)) * (A + B) :=
      ((Commute.refl (A + B)).smul_right (-s)).exp_right.eq
    have hwB : exp (s • A) * B = B * exp (s • A) + s • (C * exp (s • A)) := by
      rw [exp_smul_mul_eq A B hA s, add_mul, smul_mul_assoc]
    have hzB : exp (s • B) * B = B * exp (s • B) :=
      (((Commute.refl B).smul_left s).exp_left).eq
    exact bch_deriv_algebraic (exp ((-(s ^ 2 / 2)) • C)) (exp ((-s) • (A + B))) (exp (s • A))
      (exp (s • B)) A B C s hCv hSv hwB hzB
  have hconst : H t = H 0 :=
    is_const_of_deriv_eq_zero (fun x => (key x).differentiableAt) (fun x => (key x).deriv) t 0
  have h0 : H 0 = 1 := by simp [hH]
  have ht : exp ((-(t ^ 2 / 2)) • C) * exp ((-t) • (A + B)) * exp (t • A) * exp (t • B) = 1 :=
    hconst.trans h0
  have hcancel : (exp (t • (A + B)) * exp ((t ^ 2 / 2) • C))
      * (exp ((-(t ^ 2 / 2)) • C) * exp ((-t) • (A + B))) = 1 := by
    calc (exp (t • (A + B)) * exp ((t ^ 2 / 2) • C))
          * (exp ((-(t ^ 2 / 2)) • C) * exp ((-t) • (A + B)))
        = exp (t • (A + B))
            * ((exp ((t ^ 2 / 2) • C) * exp ((-(t ^ 2 / 2)) • C)) * exp ((-t) • (A + B))) := by
          noncomm_ring
      _ = exp (t • (A + B)) * exp ((-t) • (A + B)) := by
          rw [exp_smul_mul_exp_neg_smul C (t ^ 2 / 2), one_mul]
      _ = 1 := exp_smul_mul_exp_neg_smul (A + B) t
  calc exp (t • A) * exp (t • B)
      = ((exp (t • (A + B)) * exp ((t ^ 2 / 2) • C))
          * (exp ((-(t ^ 2 / 2)) • C) * exp ((-t) • (A + B)))) * (exp (t • A) * exp (t • B)) := by
        rw [hcancel, one_mul]
    _ = (exp (t • (A + B)) * exp ((t ^ 2 / 2) • C))
          * (exp ((-(t ^ 2 / 2)) • C) * exp ((-t) • (A + B)) * exp (t • A) * exp (t • B)) := by
        noncomm_ring
    _ = exp (t • (A + B)) * exp ((t ^ 2 / 2) • C) := by rw [ht, mul_one]

/-- **Special case of the Baker–Campbell–Hausdorff formula.**
If the commutator `[A, B] = A * B - B * A` commutes with both `A` and `B` (in particular, if it is
central), then `e^A e^B = e^{A + B + ½ [A, B]}` in a Banach algebra. -/
theorem bcH_special (A B : 𝔸) (hA : Commute (A * B - B * A) A)
    (hB : Commute (A * B - B * A) B) :
    exp A * exp B = exp (A + B + (2⁻¹ : ℝ) • (A * B - B * A)) := by
  have h := exp_smul_mul_exp_smul A B hA hB 1
  simp only [one_smul, one_pow] at h
  rw [h, show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
    ← exp_add_of_commute ((hA.add_right hB).symm.smul_right (2⁻¹ : ℝ))]

end

end QPhys

